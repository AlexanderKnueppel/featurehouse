package composer.rules.meta;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import metadata.CompositionMetadataStore;

import composer.CompositionConstants;
import composer.rules.AbstractCompositionRule;

import de.ovgu.cide.fstgen.ast.FSTNonTerminal;
import de.ovgu.cide.fstgen.ast.FSTTerminal;

/**
 * Composition of accessible clauses for invariants.
 * 
 * @author Stefan Krueger
 * @author Sebastian Krieter
 */
public class AccessibleCompositionMeta extends AbstractCompositionRule {

	public final static String COMPOSITION_RULE_NAME = "ClassAccessibleComposition";
	private static final String ACCESSIBLE_INV = "accessible \\inv:";
	private final CompositionMetadataStore metadata = CompositionMetadataStore.getInstance();

	@Override
	public void compose(final FSTTerminal terminalA, final FSTTerminal terminalB, final FSTTerminal terminalComp, final FSTNonTerminal nonterminalParent) {
		final Set<String> locSet = new HashSet<>();

		addLocations(terminalA, locSet);
		addLocations(terminalB, locSet);

		if (locSet.contains(CompositionConstants.EVERYTHING)) {
			locSet.clear();
			locSet.add(CompositionConstants.EVERYTHING);
		} else {
			locSet.remove(CompositionConstants.NOTHING);
		}

		final StringBuilder accGen = new StringBuilder(ACCESSIBLE_INV);
		accGen.append(" ");
		for (final String el : locSet) {
			accGen.append(el);
			accGen.append(CompositionConstants.COMMA_SEP);
		}
		terminalComp.setBody(accGen.toString());
	}

	@Override
	public String getRuleName() {
		return COMPOSITION_RULE_NAME;
	}

	@Override
	public void postCompose(final FSTTerminal child) {
		final StringBuilder acc = new StringBuilder(child.getBody());
		final int lastSemicolon = acc.lastIndexOf(CompositionConstants.SEMICOLON);
		if (lastSemicolon > 0) {
			acc.replace(lastSemicolon, lastSemicolon + 1, CompositionConstants.COMMA_SEP);
		}
		for (final String feature : metadata.getFeatures()) {
			acc.append(CompositionConstants.FM_MODEL + feature.toLowerCase() + CompositionConstants.COMMA_SEP);
		}

		acc.replace(acc.length() - CompositionConstants.COMMA_SEP.length(), acc.length(), CompositionConstants.SEMICOLON);
		child.setBody(acc.toString());
	}

	private void addLocations(final FSTTerminal terminal, final Set<String> locSet) {
		final String body = terminal.getBody().trim();
		Collections.addAll(locSet, body.substring(ACCESSIBLE_INV.length(), body.length() - 1).trim().split(CompositionConstants.REGEX_COMMA_WS));
	}
}
