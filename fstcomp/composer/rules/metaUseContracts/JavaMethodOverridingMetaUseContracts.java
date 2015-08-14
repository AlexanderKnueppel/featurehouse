package composer.rules.metaUseContracts;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.StringTokenizer;

import metadata.CompositionMetadataStore;

import composer.CompositionException;
import composer.rules.JavaMethodOverriding;
import composer.rules.meta.JavaMethodMeta;

import de.ovgu.cide.fstgen.ast.FSTNode;
import de.ovgu.cide.fstgen.ast.FSTNonTerminal;
import de.ovgu.cide.fstgen.ast.FSTTerminal;

/**
 * Extends the standard {@link JavaMethodOverriding} to generate a meta product. Adds dispatcher method for each refinement to check whether
 * the corresponding feature is not selected.
 * 
 * @author Stefan Krueger
 * 
 */

public class JavaMethodOverridingMetaUseContracts extends JavaMethodMeta {

	final String lineEnding = System.getProperty("line.separator", "\n");
	final char marker = '$';

	@Override
	public void compose(FSTTerminal terminalA, FSTTerminal terminalB, FSTTerminal terminalComp, FSTNonTerminal nonterminalParent) throws CompositionException {

		CompositionMetadataStore meta = CompositionMetadataStore.getInstance();
		/* Create dispatcher method For refinement */
		final String methodName = getMethodName(terminalA);

		final String dispMethodTitle = terminalA.getName().replaceAll(methodName, "dispatch_" + methodName + "_" + terminalA.getOriginalFeatureName());
		final String returnType = getReturnType(terminalA.getBody(), methodName);

		/*
		 * check whether there is a domain method for previous refinement (in case it's the first merge) and create domain method if
		 * necessary
		 */
		// TODO: check for differences regarding modifiers
		// Collections.<String>emptyList();
		boolean isFirstMerge = true;
		for (FSTNode child : terminalComp.getParent().getParent().getChildren()) {
			if (child.getName().equals(methodName + "_" + terminalB.getOriginalFeatureName())
					&& returnType.equals(getReturnType(((FSTTerminal) ((FSTNonTerminal) child).getChildren().get(2)).getBody(),
							methodName + "_" + terminalB.getOriginalFeatureName()))) {
				isFirstMerge = false;
				break;
			}
		}
		
		final String aParameterNames = getParameterNames(terminalA);
		final String[] parameterNames = aParameterNames.split(", ");
		final String[] parameterTypes = dispMethodTitle.substring(dispMethodTitle.indexOf("(") + 1).split("-");
		StringBuilder parameters = new StringBuilder("");
		for (int i = 0; i < parameterNames.length; i++) {
			parameters.append(parameterTypes[2 * i]);
			parameters.append(" ");
			parameters.append(parameterNames[i]);
			if (i < parameterNames.length - 1) {
				parameters.append(",");
			}
		}

		/*
		 * Body of dispatcher method Check whether the necessary feature is selected And Call right method.
		 */
		final String dispMethodName = dispMethodTitle.substring(0, dispMethodTitle.indexOf("("));
		final String aFeatureName = terminalA.getFeatureName();
		final String bFeatureName = terminalB.getOriginalFeatureName();

		final int ind = terminalB.getBody().indexOf("{") + 1;
		if (terminalB.getBody().charAt(ind) == marker) {
			FSTNonTerminal dispParent = (FSTNonTerminal) terminalB.getParent().getDeepClone();
			dispParent.setName(dispMethodName.replace(aFeatureName, bFeatureName));
			terminalComp.getParent().getParent().addChild(dispParent);
			FSTTerminal term = (FSTTerminal) dispParent.getChildren().get(2);
			term.setName(dispMethodName.replace(aFeatureName, bFeatureName));
			term.setBody(term.getBody().replaceFirst(methodName, dispMethodName.replace(aFeatureName, bFeatureName)));
			meta.putMapping(methodName, (terminalB.getOriginalFeatureName()), dispParent.getName());
		}

		final String ret = !returnType.isEmpty() ? "return " : "";
		final String previousMethodName = isFirstMerge ? methodName + "_" + bFeatureName : dispMethodName.replace(aFeatureName, bFeatureName);
		terminalComp.setBody((returnType.isEmpty() ? "void" : returnType) + " " + methodName + "("
				+ (parameters.toString().contains("{") ? "" : parameters.toString()) + "){" + marker + lineEnding + "\t\tif (FM.FeatureModel."
				+ getLowFeatureName(terminalA) + ") {" + lineEnding + "\t\t\t" + ret + methodName + "_" + aFeatureName + "(" + aParameterNames + ");"
				+ lineEnding + "\t\t" + "} else {" + lineEnding + "\t\t\t" + ret + previousMethodName + "(" + aParameterNames + ");" + lineEnding + "\t\t}"
				+ lineEnding + "\t}");
		final String domainMethodName = getMethodName(terminalA) + "_" + terminalA.getFeatureName();
		
		if (isFirstMerge) {
			//Create Domain method for method introduction  
			final FSTNonTerminal domainNonTerminalB = addDomainMethod((FSTNonTerminal)terminalComp.getParent().getDeepClone(), terminalB, previousMethodName, domainMethodName, true);
			terminalComp.getParent().getParent().addChild(domainNonTerminalB);
			meta.putMapping("", (terminalB.getOriginalFeatureName()), domainNonTerminalB.getName());
		}
		
		/* Create Domain Method of current refinement */
		terminalComp.getParent().getParent().addChild(addDomainMethod((FSTNonTerminal)terminalComp.getParent().getDeepClone(), terminalA, previousMethodName, domainMethodName, false));
		meta.putMapping("", (terminalB.getOriginalFeatureName()), domainMethodName);

		//TODO: Check whether this is actually necessary
		List<FSTNode> children = terminalComp.getParent().getChildren();
		Set<FSTTerminal> tmpchildren = new HashSet<FSTTerminal>();
		for (FSTNode child : children) {
			/*
			 * iterate through all children of tmpComp.getParent() and check whether child.getFeatureName().equals(terminalB.getFeatureName)
			 */
			if (child instanceof FSTTerminal) {
				FSTTerminal term = (FSTTerminal) child;
				if (term.getOriginalFeatureName().equals(bFeatureName)) {
					tmpchildren.add(term);
				}
			}
		}
		terminalComp.getParent().getChildren().removeAll(tmpchildren);
	}

	private FSTNonTerminal addDomainMethod(FSTNonTerminal nonTerminal, FSTTerminal terminalA, final String previousMethodName, String domainMethodName, boolean first) {
		if (first) {
			domainMethodName = previousMethodName;
		}
		FSTTerminal domainTerminal = (FSTTerminal) terminalA.getDeepClone();

		nonTerminal.setName(domainMethodName);
		domainTerminal.setName(domainMethodName);
		domainTerminal.setBody(terminalA.getBody().replaceFirst(getMethodName(terminalA), domainMethodName));

		if (super.replaceOriginal(terminalA) && !first) {
			domainTerminal.setBody(domainTerminal.getBody().replace("original(", previousMethodName+ "("));
		}
		nonTerminal.addChild(domainTerminal);
		return nonTerminal;
	}

	private String getMethodName(FSTTerminal terminalA) {
		String methodName = terminalA.getName();
		StringTokenizer st = new StringTokenizer(methodName, "(");
		if (st.hasMoreTokens()) {
			methodName = st.nextToken();
		}
		return methodName;
	}

	public static String getFeatureName(FSTNode node) {
		if (node.getType().equals("Feature"))
			return node.getName().toLowerCase();
		else
			return getFeatureName(node.getParent());
	}

	protected String getLowFeatureName(FSTNode node) {
		return getFeatureName(node).toLowerCase();
	}

	@Override
	public void postCompose(FSTTerminal child) {
		super.postCompose(child);
		String body = child.getBody();
		child.setBody(body.replace("{" + marker, "{"));
	}
}
