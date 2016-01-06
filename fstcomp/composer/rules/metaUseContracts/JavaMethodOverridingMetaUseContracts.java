package composer.rules.metaUseContracts;

import static composer.CompositionConstants.*;

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
 */

public class JavaMethodOverridingMetaUseContracts extends JavaMethodMeta {

	static final char domDispMethodMarker = '$';

	@Override
	public void compose(final FSTTerminal terminalA, final FSTTerminal terminalB, final FSTTerminal terminalComp, final FSTNonTerminal nonterminalParent)
			throws CompositionException {
		/* Create dispatcher method
		 * Method checks whether the necessary feature is selected and call respective domain method.
		 */
		final String aFeatureName = terminalA.getOriginalFeatureName();
		final String bFeatureName = terminalB.getOriginalFeatureName();
		final String methodName = getMethodName(terminalA);
		final String dispMethodTitle = terminalA.getName().replace(methodName, DISPATCH_ + methodName + _ + terminalA.getOriginalFeatureName());
		final String oldDispMethodName = dispMethodTitle.substring(0, dispMethodTitle.indexOf(LBRACE)).replace(aFeatureName, bFeatureName);
		final String terminalBBody = terminalB.getBody();

		if (terminalBBody.charAt(terminalBBody.indexOf("{") + 1) == domDispMethodMarker) {
			final FSTNonTerminal dispParent = (FSTNonTerminal) terminalB.getParent().getDeepClone();
			dispParent.setName(oldDispMethodName);
			terminalComp.getParent().getParent().addChild(dispParent);
			final FSTTerminal term = (FSTTerminal) dispParent.getChildren().get(FST_METHOD_INDEX);
			term.setName(oldDispMethodName);
			term.setBody(term.getBody().replaceFirst(methodName, oldDispMethodName));
		}

		/* Check whether this is the first composition. */
		String previousMethodName = methodName + _ + bFeatureName;
		final String returnType = getReturnType(terminalA.getBody(), methodName);
		boolean isFirstMerge = true;
		for (final FSTNode child : terminalComp.getParent().getParent().getChildren()) {
			if (child.getName().equals(previousMethodName)
					&& returnType.equals(getReturnType(((FSTTerminal) ((FSTNonTerminal) child).getChildren().get(FST_METHOD_INDEX)).getBody(),
							previousMethodName))) {
				isFirstMerge = false;
				previousMethodName = oldDispMethodName;
				break;
			}
		}
		/* Set new body for method that is propagated through composition (i.e., dispatcher method that is currently the highest in the call hierarchy).*/
		terminalComp.setBody(getNewBody(terminalA, previousMethodName, returnType).toString());

		if (isFirstMerge) {
			/* Create domain method for method introduction */
			final FSTNonTerminal domainNonTerminalB = addDomainMethod((FSTNonTerminal) terminalComp.getParent().getDeepClone(), terminalB, previousMethodName);
			terminalComp.getParent().getParent().addChild(domainNonTerminalB);
		}

		/* Create domain method of current refinement */
		terminalComp.getParent().getParent().addChild(
			addDomainMethod((FSTNonTerminal) terminalComp.getParent().getDeepClone(), terminalA, methodName + _ + aFeatureName, previousMethodName));
	}

	@Override
	public void postCompose(final FSTTerminal child) {
		super.postCompose(child);
		final String body = child.getBody();
		child.setBody(body.replace("{" + domDispMethodMarker, "{"));
	}

	@Override
	protected String getLowFeatureName(final FSTNode node) {
		return getFeatureName(node).toLowerCase();
	}

	private FSTNonTerminal addDomainMethod(final FSTNonTerminal nonTerminal, final FSTTerminal terminalA, final String domainMethodName) {
		final FSTTerminal domainTerminal = (FSTTerminal) terminalA.getDeepClone();

		nonTerminal.setName(domainMethodName);
		domainTerminal.setName(domainMethodName);
		domainTerminal.setBody(terminalA.getBody().replaceFirst(getMethodName(terminalA), domainMethodName));

		nonTerminal.addChild(domainTerminal);
		return nonTerminal;
	}

	private FSTNonTerminal addDomainMethod(final FSTNonTerminal nonTerminal, final FSTTerminal terminalA, final String domainMethodName,
			final String previousMethodName) {
		final FSTNonTerminal retNT = addDomainMethod(nonTerminal, terminalA, domainMethodName);
		if (super.replaceOriginal(terminalA)) {
			final FSTTerminal domainTerminal = (FSTTerminal) retNT.getChildren().get(retNT.getChildren().size() - 1);
			domainTerminal.setBody(domainTerminal.getBody().replace(ORIGINAL_CALL, previousMethodName + LBRACE));
		}
		return retNT;
	}

	private String getNewBody(final FSTTerminal terminal, final String previousMethodName, final String returnType) {
		final String ret = returnType.isEmpty() ? "" : RETURN;
		final String terminalABody = terminal.getBody();
		final String parameters = terminalABody.substring(terminalABody.indexOf(LBRACE) + 1, terminalABody.indexOf(RBRACE)).trim();
		final String aParameterNames = getParameterNames(terminal);
		final String methodName = getMethodName(terminal);

		final StringBuilder newBodySB = new StringBuilder();
		// method signature
		newBodySB.append(returnType.isEmpty() ? VOID : returnType).append(WS).append(methodName);
		newBodySB.append(LBRACE).append(parameters.contains("{") ? "" : parameters).append(") {").append(domDispMethodMarker).append(NEWLINE);

		// if-statement checking whether a feature variable is enabled
		newBodySB.append("\t\tif (");
		newBodySB.append(FM_MODEL);
		newBodySB.append(getLowFeatureName(terminal));
		newBodySB.append(") {").append(NEWLINE);

		//body of if branch
		newBodySB.append("\t\t\t").append(ret).append(methodName).append(_).append(terminal.getOriginalFeatureName());
		newBodySB.append(LBRACE).append(aParameterNames).append(RBRACE);
		newBodySB.append(SEMICOLON).append(NEWLINE);

		//body of else branch
		newBodySB.append("\t\t} else {").append(NEWLINE);
		newBodySB.append("\t\t\t").append(ret).append(previousMethodName);
		newBodySB.append(LBRACE).append(aParameterNames).append(RBRACE).append(SEMICOLON).append(NEWLINE);
		newBodySB.append("\t\t}").append(NEWLINE);

		//end of method
		newBodySB.append("\t}");
		return newBodySB.toString();
	}
}
