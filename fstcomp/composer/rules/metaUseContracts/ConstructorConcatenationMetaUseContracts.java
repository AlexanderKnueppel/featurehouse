package composer.rules.metaUseContracts;

import composer.CompositionConstants;
import composer.rules.ConstructorConcatenation;
import composer.rules.meta.JavaMethodMeta;
import composer.rules.meta.JavaMethodOverridingMeta;

import de.ovgu.cide.fstgen.ast.FSTNode;
import de.ovgu.cide.fstgen.ast.FSTNonTerminal;
import de.ovgu.cide.fstgen.ast.FSTTerminal;

/**
 * Constructor composition for metaproduct
 * 
 * @author Stefan Krueger
 * 
 */
public class ConstructorConcatenationMetaUseContracts extends ConstructorConcatenation {

	private static final String IF_FM_FEATURE_MODEL = "if " + CompositionConstants.LBRACE + CompositionConstants.FM_MODEL;
	private static final String VOID_HELPER = CompositionConstants.VOID + " /*@helper@*/ ";

	@Override
	public void compose(final FSTTerminal terminalA, final FSTTerminal terminalB, final FSTTerminal terminalComp, final FSTNonTerminal nonterminalParent) {
		boolean isFirstMerge = true;
		for (final FSTNode child : terminalComp.getParent().getParent().getChildren()) {
			if (child.getName().startsWith(JavaMethodMeta.getMethodName(terminalB) + CompositionConstants._ + terminalB.getOriginalFeatureName())) {
				isFirstMerge = false;
				break;
			}
		}
		final String body = terminalB.getBody();
		final StringBuilder firstBodyPart;
		if (isFirstMerge) {
			firstBodyPart = new StringBuilder(body.substring(0, body.indexOf("{") + 1));
			addDomainConstructor(terminalB, terminalComp, firstBodyPart);
		} else {
			firstBodyPart = new StringBuilder(body.substring(0, body.lastIndexOf("}")));
		}
		addDomainConstructor(terminalA, terminalComp, firstBodyPart);
		firstBodyPart.append("\t}");

		terminalComp.setBody(firstBodyPart.toString());
	}

	private void addDomainConstructor(final FSTTerminal terminal, final FSTTerminal terminalComp, StringBuilder firstBodyPart) {
		final FSTNonTerminal parent = (FSTNonTerminal) terminal.getParent().getDeepClone();
		final FSTTerminal term = (FSTTerminal) parent.getChildren().get(2);
		final String constrName = term.getName();
		final String firstNamePart = constrName.substring(0, constrName.indexOf(CompositionConstants.LBRACE)) + CompositionConstants._;
		final String aName = firstNamePart + terminal.getOriginalFeatureName() + constrName.substring(constrName.indexOf(CompositionConstants.LBRACE));
		final String aParameterNames = JavaMethodOverridingMeta.getParameterNames(terminal);
		
		parent.setName(aName);
		term.setName(aName);
		
		term.setBody(terminal.getBody().replace(constrName.substring(0, constrName.indexOf(CompositionConstants.LBRACE)),
				VOID_HELPER + firstNamePart + terminal.getOriginalFeatureName()));
		terminalComp.getParent().getParent().addChild(parent);

		firstBodyPart.append(CompositionConstants.NEWLINE);
		firstBodyPart.append("\t\t").append(IF_FM_FEATURE_MODEL).append(getLowFeatureName(terminal)).append(") {").append(CompositionConstants.NEWLINE);
		firstBodyPart.append("\t\t\t").append(firstNamePart).append(terminal.getOriginalFeatureName()).append(CompositionConstants.LBRACE)
				.append(aParameterNames.contains("{") ? "" : aParameterNames).append(");").append(CompositionConstants.NEWLINE);
		firstBodyPart.append("\t\t}").append(CompositionConstants.NEWLINE);
	}

	@Override
	public String getRuleName() {
		return COMPOSITION_RULE_NAME;
	}

	protected String getLowFeatureName(final FSTNode node) {
		return JavaMethodOverridingMeta.getFeatureName(node).toLowerCase();
	}
}
