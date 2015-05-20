package composer.rules;

import de.ovgu.cide.fstgen.ast.FSTNonTerminal;
import de.ovgu.cide.fstgen.ast.FSTTerminal;

/**
 * Replacing keyword original in contracts 
 *
 */
public class ExpansionOverriding extends AbstractCompositionRule {
	public final static String COMPOSITION_RULE_NAME = "ExpansionOverriding";
	public void compose(FSTTerminal terminalA, FSTTerminal terminalB, FSTTerminal terminalComp, FSTNonTerminal nonterminalParent) {
		String bodyA = terminalA.getBody();
		String bodyB = terminalB.getBody();
		
		String pattern = "\\s*original\\s*\\(\\s*\\)\\s*";
		bodyB = bodyB.trim();
			
		if(bodyB.length() > 0 && ((bodyB.charAt(0) == '{' && bodyB.charAt(bodyB.length() - 1) == '}') || (bodyB.charAt(0) == '(' && bodyB.charAt(bodyB.length() - 1) == ')')))
			bodyB = bodyB.substring(1, bodyB.length() - 1);

		String compBody = bodyA.replaceAll(pattern, bodyB);
		terminalComp.setBody(compBody);

	}
}
