package composer.rules.metaUseContracts;

import composer.FSTGenComposerExtension;
import composer.rules.ConstructorConcatenation;

import de.ovgu.cide.fstgen.ast.FSTNode;
import de.ovgu.cide.fstgen.ast.FSTNonTerminal;
import de.ovgu.cide.fstgen.ast.FSTTerminal;

public class ConstructorConcatenationMetaUseContracts extends ConstructorConcatenation {

	@Override
	public void compose(FSTTerminal terminalA, FSTTerminal terminalB, FSTTerminal terminalComp, FSTNonTerminal nonterminalParent) {

		String body = terminalB.getBody();
		StringBuilder firstBodyPart = new StringBuilder(body.substring(0, body.lastIndexOf("}")));

		//TODO: Extract method
		FSTNonTerminal parent = (FSTNonTerminal) terminalA.getParent().getDeepClone();
		FSTTerminal term = (FSTTerminal) parent.getChildren().get(2);
		final String constrName = term.getName();
		final String firstNamePart = constrName.substring(0, constrName.indexOf("(")) + "_";
		final String aName = firstNamePart + terminalA.getOriginalFeatureName() + constrName.substring(constrName.indexOf("("));
		parent.setName(aName);
		term.setName(aName);
		final String aParameterNames = getParameterNames(terminalA);
		term.setBody(terminalA.getBody()
				.replace(constrName.substring(0, constrName.indexOf("(")), "void " + firstNamePart + terminalA.getOriginalFeatureName()));
		terminalComp.getParent().getParent().addChild(parent);

		boolean isFirstMerge = true;
		for (FSTNode child : terminalComp.getParent().getParent().getChildren()) {
			if (child.getName().startsWith(firstNamePart + terminalB.getOriginalFeatureName())) {
				isFirstMerge = false;
			}
		}

		if (isFirstMerge) {
			FSTNonTerminal parentB = (FSTNonTerminal) terminalB.getParent().getDeepClone();
			FSTTerminal termB = (FSTTerminal) parentB.getChildren().get(2);
			String bName = firstNamePart + terminalB.getOriginalFeatureName() + constrName.substring(constrName.indexOf("("));
			parentB.setName(bName);
			termB.setName(bName);
			termB.setBody(terminalB.getBody().replace(constrName.substring(0, constrName.indexOf("(")),
					"void " + firstNamePart + terminalB.getOriginalFeatureName()));
			terminalComp.getParent().getParent().addChild(parentB);

			final String bParameterNames = getParameterNames(terminalB);
			firstBodyPart = new StringBuilder(body.substring(0, body.indexOf("{") + 1));
			firstBodyPart.append("\n\t\tif (FM.FeatureModel." + terminalB.getOriginalFeatureName().toLowerCase() + ") {\n\t\t\t" + firstNamePart
					+ terminalB.getOriginalFeatureName() + "(" + (bParameterNames.contains("{") ? "" : bParameterNames) + ");\n\t\t}\n\t");
		}

		firstBodyPart.append("\tif (FM.FeatureModel." + getLowFeatureName(terminalA) + ") {\n\t\t\t" + firstNamePart + terminalA.getOriginalFeatureName() + "("
				+ (aParameterNames.contains("{") ? "" : aParameterNames) + ");\n\t\t}");
		firstBodyPart.append("\n\t}");
		terminalComp.setBody(firstBodyPart.toString());
	}

	protected String getLowFeatureName(FSTNode node) {
		return getFeatureName(node).toLowerCase();
	}

	private static String getFeatureName(FSTNode node) {
		if (node.getType().equals("Feature")) {
			return node.getName() + (FSTGenComposerExtension.key ? "" : "()");
		} else {
			return getFeatureName(node.getParent());
		}
	}

	@Override
	public String getRuleName() {
		return COMPOSITION_RULE_NAME;
	}

	protected String getParameterNames(FSTTerminal terminalA) {
		String parameter = terminalA.getBody().substring(terminalA.getBody().indexOf('(') + 1, terminalA.getBody().indexOf(')')).trim();
		String parameterNames = "";
		String[] p = parameter.split("[,]");
		for (int i = 0; i < p.length; i++) {
			String[] split = p[i].trim().split("[ ]");
			if (split.length < 2) {
				continue;
			}
			parameterNames += split[split.length - 1];
			if (i < p.length - 1) {
				parameterNames += ", ";
			}
		}
		return parameterNames;
	}

	protected String getReturnType(String body, String name) {
		// remove @annotations
		body = body.replaceAll("@\\w*\\W*", "");
		// remove spaces between name and ()
		body = body.replaceAll(name + "\\W*\\(", name + "(");
		body = body.substring(0, body.indexOf(name + "("));
		body = body.split("[ ]")[body.split("[ ]").length - 1];
		body = body.replaceAll(" ", "");
		if (body.equals("void")) {
			return "";
		}
		return body;
	}
}
