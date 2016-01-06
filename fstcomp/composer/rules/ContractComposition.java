package composer.rules;

import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import composer.CompositionConstants;
import composer.CompositionException;
import composer.FSTGenComposer;

import de.ovgu.cide.fstgen.ast.FSTNode;
import de.ovgu.cide.fstgen.ast.FSTNonTerminal;
import de.ovgu.cide.fstgen.ast.FSTTerminal;

public class ContractComposition extends AbstractCompositionRule {

	public final static String COMPOSITION_RULE_NAME = "ContractComposition";

	protected String contractStyle = CompositionConstants.PLAIN_CONTRACTING;
	private ContractReader contractReader;

	public ContractComposition(final String contract_style) {
		if (contract_style != null) {
			contractStyle = contract_style.trim();
		}
	}

	public boolean checkContainsOriginal(final FSTTerminal terminal) {
		final String body = terminal.getBody();
		return (body.contains(CompositionConstants.ORIGINAL_CASE_KEYWORD) || body.contains(CompositionConstants.ORIGINAL_SPEC_KEYWORD) || body
				.contains(CompositionConstants.ORIGINAL_KEYWORD));
	}

	@Override
	public void compose(final FSTTerminal terminalA, final FSTTerminal terminalB, final FSTTerminal terminalComp, final FSTNonTerminal nonterminalParent)
			throws CompositionException {
		// Check Composition style
		if (contractStyle.equals(CompositionConstants.PLAIN_CONTRACTING)) {
			plainContracting(terminalA, terminalB, terminalComp);
		} else if (contractStyle.equals(CompositionConstants.CONTRACT_OVERRIDING)) {
			contractOverriding(terminalA, terminalB, terminalComp);
		} else if (contractStyle.equals(CompositionConstants.EXPLICIT_CONTRACTING)) {
			explicitContracting(terminalA, terminalB, terminalComp);
		} else if (contractStyle.equals(CompositionConstants.CONSECUTIVE_CONTRACTING)) {
			consecutiveContracting(terminalA, terminalB, terminalComp);
		} else if (contractStyle.equals(CompositionConstants.CUMULATIVE_CONTRACTING)) {
			cumulativeContracting(terminalA, terminalB, terminalComp);
		} else if (contractStyle.equals(CompositionConstants.CONJUNCTIVE_CONTRACTING)) {
			conjunctiveContracting(terminalA, terminalB, terminalComp);
		} else if (contractStyle.equals(CompositionConstants.METHOD_BASED_COMPOSITION)) {
			compositionByKeywords(terminalA, terminalB, terminalComp, nonterminalParent);
		}

		// Does the composition contains non jml keywords?
		if (checkContainsOriginal(terminalComp)) {
			throw new CompositionException(terminalA, terminalB,
					"Contract still contains the keyword \\original, \\original_case or \\original_spec after composition!");
		}
	}

	@Override
	public String getRuleName() {
		return COMPOSITION_RULE_NAME;
	}

	// Check Keywords in Method-Based Contract Composition
	protected void compositionByKeywords(final FSTTerminal terminalA, final FSTTerminal terminalB, final FSTTerminal terminalComp,
			final FSTNonTerminal nonterminalParent) {
		String compositionKey = "";

		for (final FSTNode n : terminalB.getParent().getChildren()) {
			if (n.getType().equals("ContractCompKey")) {
				compositionKey = ((FSTTerminal) n).getContractCompKey();
				break;
			}
		}

		if (compositionKey.equals(CompositionKeyword.FINAL_CONTRACT.getLabel()) || compositionKey.equals(CompositionKeyword.FINAL_METHOD.getLabel())) {
			plainContracting(terminalA, terminalB, terminalComp);
		} else if (compositionKey.equals(CompositionKeyword.CONSECUTIVE_CONTRACT.getLabel())) {
			consecutiveContracting(terminalA, terminalB, terminalComp);
		} else if (compositionKey.equals(CompositionKeyword.CONJUNCTIVE_CONTRACT.getLabel())) {
			conjunctiveContracting(terminalA, terminalB, terminalComp);
		} else if (compositionKey.equals(CompositionKeyword.CUMULATIVE_CONTRACT.getLabel())) {
			cumulativeContracting(terminalA, terminalB, terminalComp);
		} else {
			explicitContracting(terminalA, terminalB, terminalComp);
		}
	}

	protected void conjunctiveContracting(final FSTTerminal terminalA, final FSTTerminal terminalB, final FSTTerminal terminalComp) {
		if (terminalB.getBody().contains("also")) {
			desugarAlso(terminalB);
		}
		if (terminalA.getBody().contains("also")) {
			desugarAlso(terminalA);
		}
		final List<FSTTerminal> reqClaB = getRequiresClauses(terminalB);
		final List<FSTTerminal> reqClaA = getRequiresClauses(terminalA);
		final List<FSTTerminal> ensClaB = getEnsuresClauses(terminalB);
		final List<FSTTerminal> ensClaA = getEnsuresClauses(terminalA);

		terminalComp.setBody(joinClauses(reqClaB, reqClaA, "requires", "&&") + "\n\t " + joinClauses(ensClaB, ensClaA, "ensures", "&&"));
	}

	protected void consecutiveContracting(final FSTTerminal terminalA, final FSTTerminal terminalB, final FSTTerminal terminalComp) {
		terminalComp.setBody(terminalB.getBody() + "\n\talso\n\t " + terminalA.getBody());
	}

	protected void contractOverriding(final FSTTerminal terminalA, final FSTTerminal terminalB, final FSTTerminal terminalComp) {
		terminalComp.setBody(terminalA.getBody());
	}

	protected void cumulativeContracting(final FSTTerminal terminalA, final FSTTerminal terminalB, final FSTTerminal terminalComp) {
		if (terminalB.getBody().contains("also")) {
			desugarAlso(terminalB);
		}
		if (terminalA.getBody().contains("also")) {
			desugarAlso(terminalA);
		}

		final List<FSTTerminal> reqClaB = getRequiresClauses(terminalB);
		final List<FSTTerminal> reqClaA = getRequiresClauses(terminalA);
		final List<FSTTerminal> ensClaB = getEnsuresClauses(terminalB);
		final List<FSTTerminal> ensClaA = getEnsuresClauses(terminalA);

		terminalComp.setBody(joinClauses(reqClaB, reqClaA, "requires", "||") + "\n\t " + joinClauses(ensClaB, ensClaA, "ensures", "&&"));
	}

	protected void desugarAlso(final FSTTerminal terminal) {
		final String[] baseCases = terminal.getBody().trim().split("also");

		final StringBuilder reqBuilder = new StringBuilder("requires ");
		final StringBuilder ensBuilder = new StringBuilder("ensures ");
		for (final String ca : baseCases) {
			final FSTTerminal temp = new FSTTerminal(terminal.getType(), terminal.getName(), ca, "");
			final List<FSTTerminal> reqCla = getRequiresClauses(temp);
			final List<FSTTerminal> ensCla = getEnsuresClauses(temp);

			if ((reqCla.size() > 0) && (ensCla.size() > 0)) {
				final String reqTemp = joinClause(reqCla, "requires");
				reqBuilder.append(reqTemp).append(" || ");
				ensBuilder.append("(\\old").append(reqTemp).append("\n\t\t ==> ").append(joinClause(getEnsuresClauses(temp), "ensures")).append(") && ");

			} else if (reqCla.size() > 0) {
				reqBuilder.append(joinClause(reqCla, "requires")).append(" || ");
			} else if (ensCla.size() > 0) {
				ensBuilder.append(joinClause(getEnsuresClauses(temp), "ensures")).append(" && ");
			}
		}
		reqBuilder.replace(reqBuilder.lastIndexOf(" || "), reqBuilder.lastIndexOf(" || ") + 4, ";");
		ensBuilder.replace(ensBuilder.lastIndexOf(" && "), ensBuilder.lastIndexOf(" && ") + 4, ";");
		terminal.setBody(reqBuilder.toString() + "\n\t" + ensBuilder.toString());
	}

	protected void explicitContracting(final FSTTerminal terminalA, final FSTTerminal terminalB, final FSTTerminal terminalComp) {
		terminalComp.setBody(getReplacementString(terminalA, terminalB));
	}

	protected List<FSTTerminal> getEnsuresClauses(final FSTTerminal terminal) {
		contractReader = new ContractReader(terminal);
		return contractReader.getEnsuresClauses();
	}

	/**
	 * Determines the method name for a {@link FSTNode} of a method specification
	 * 
	 * @param node specification node
	 * @return method name
	 */
	protected String getMethodName(final FSTNode node) {
		if (node == null) {
			return "";
		}
		if (node.getType().equals("MethodDeclarationWithSpec")) {
			String name = node.getName();
			if (name.contains("(")) {
				name = name.substring(0, name.indexOf("(")).trim();
			}
			return name;
		}
		return getMethodName(node.getParent());
	}

	protected String getOriginalCaseReplacement(final String[] baseCases, final int caseId) {
		return baseCases[caseId];
	}

	protected String getOriginalReplacement(final String[] baseCases, final int caseId, final String prefix) {
		final StringBuffer result = new StringBuffer();
		if (caseId >= baseCases.length) {
			throw new RuntimeException("Original() reference cannot be satisfied, specification case: # " + caseId);
		}

		final String[] prefixes = new String[baseCases.length];
		for (int i = 0; i < baseCases.length; i++) {

			prefixes[i] = prefixes[i] + "behavior ";

			String baseCase = baseCases[i].replaceAll("@", "").trim();

			if (baseCase.startsWith("public ")) {
				prefixes[i] = "public ";
				baseCase = baseCase.substring(7);
			} else if (baseCase.startsWith("private ")) {
				prefixes[i] = "private ";
				baseCase = baseCase.substring(8);
			} else if (baseCase.startsWith("protected ")) {
				prefixes[i] = "protected ";
				baseCase = baseCase.substring(10);
			}

			if (baseCase.startsWith("behavior ")) {
				prefixes[i] = prefixes[i] + "behavior ";
				baseCase = baseCase.substring(9);
			} else if (baseCase.startsWith("normal_behavior ")) {
				prefixes[i] = prefixes[i] + "normal_behavior  ";
				baseCase = baseCase.substring(16);
			} else if (baseCase.startsWith("exceptional_behavior ")) {
				prefixes[i] = prefixes[i] + "exceptional_behavior  ";
				baseCase = baseCase.substring(21);
			}

			baseCases[caseId] = baseCase;
		}

		FSTGenComposer.outStream.println("baseCases(id)= " + baseCases[caseId]);
		final Pattern p = Pattern.compile(".*\\(\\\\(forall|exists|max|min|num_of|product|sum)[^;]*(;)[^;]*(;).*\\).*", Pattern.DOTALL);

		Matcher m = p.matcher(baseCases[caseId]);

		while (m.find()) {
			for (int i = 2; i <= m.groupCount(); i++) {
				final StringBuilder sb = new StringBuilder(baseCases[caseId]);
				sb.setCharAt(m.start(i), '#');
				baseCases[caseId] = sb.toString();
			}
			m = p.matcher(baseCases[caseId]);
			FSTGenComposer.outStream.println("XX " + baseCases[caseId]);
		}
		final String[] clausesA = baseCases[caseId].trim().split(";");

		boolean append = false;
		for (int i = 0; i < clausesA.length; i++) {

			if (clausesA[i].trim().startsWith(prefix + " ")) {
				result.append("(" + clausesA[i].trim().replaceFirst(prefix, "") + " )");

				result.append(" && ");
				append = true;
			}

		}
		if (append) {
			result.setLength(result.length() - 4);
		}

		return result.toString().replaceAll("#", ";");
	}

	protected String getOriginalSpecReplacement(final String[] baseCases) {
		final StringBuffer buf = new StringBuffer();
		boolean append = false;
		for (final String s : baseCases) {
			buf.append(s);
			buf.append("\talso");
			append = true;
		}
		if (append) {
			buf.setLength(buf.length() - 5);
		}
		return buf.toString();
	}

	protected String getReplacementString(final FSTTerminal terminalA, final FSTTerminal terminalB) {

		terminalA.setBody(terminalA.getBody().trim());
		terminalB.setBody(terminalB.getBody().trim());
		boolean isExtendingSpec = false;

		if (terminalA.getParent().getParent().getType().equals("ExtendingSpec")) {
			isExtendingSpec = true;
		}

		final String[] baseCases = terminalB.getBody().trim().split("also");

		final StringBuffer result = new StringBuffer();
		if (isExtendingSpec) {
			result.append("also\n");
		}
		result.append("\t");

		final String[] casesA = terminalA.getBody().trim().split("also");

		for (int j = 0; j < casesA.length; j++) {

			final String[] clausesA = casesA[j].trim().split(";");

			for (int i = 0; i < clausesA.length; i++) {
				if (!clausesA[i].trim().equals("")) {
					clausesA[i] = clausesA[i] + ";";
				}
			}
			for (int i = 0; i < clausesA.length; i++) {
				if (clausesA[i].contains(CompositionConstants.ORIGINAL_KEYWORD) || clausesA[i].contains(CompositionConstants.ORIGINAL_KEYWORD_CLAUSE)
						|| clausesA[i].contains(CompositionConstants.ORIGINAL_CASE_KEYWORD) || clausesA[i].contains(CompositionConstants.ORIGINAL_SPEC_KEYWORD)) {
					result.append(replaceOriginal(baseCases, clausesA[i], j, clausesA[i].replaceAll("@", "").trim().split(" ")[0]).replace(";;", ";"));
				} else {
					// no original in this clause
					result.append(clausesA[i]);
				}
			}

			if (j < (casesA.length - 1)) {
				result.append("\n\t also\n\t");
			}
		}

		return result.toString().trim()
				.replace(CompositionConstants.ORIGINAL_CALL, getMethodName(terminalA) + "__wrappee__" + terminalB.getOriginalFeatureName() + "(");
	}

	protected List<FSTTerminal> getRequiresClauses(final FSTTerminal terminal) {
		contractReader = new ContractReader(terminal);
		return contractReader.getRequiresClauses();
	}

	// Joins all Requires or Ensures clauses with an AND Operator of one
	// contract
	protected String joinClause(final List<FSTTerminal> clauses, final String clauseType) {
		final StringBuilder builder = new StringBuilder("");
		final String operationType = " && ";

		for (final FSTTerminal cl : clauses) {
			builder.append("(").append(cl.getBody().substring(0, cl.getBody().lastIndexOf(";")).replace(clauseType + " ", "")).append(")")
					.append(operationType);
		}
		builder.replace(builder.lastIndexOf(operationType), builder.lastIndexOf(operationType) + 4, "");
		if (clauses.size() > 1) {
			builder.insert(0, "(");
			builder.append(")");
		}
		return builder.toString();
	}

	// joins Either Requires or Ensures clauses (claustaype)
	// joins them using the operationtype (&& or ||)
	protected String joinClauses(final List<FSTTerminal> reqOrEnsClaB, final List<FSTTerminal> reqOrEnsClaA, final String clauseType, String operationType) {
		operationType = "\n\t\t " + operationType + " ";
		final StringBuilder builder = new StringBuilder("");

		if ((reqOrEnsClaB.size() > 0) && (reqOrEnsClaA.size() > 0)) {
			builder.append(clauseType).append(" ").append(joinClause(reqOrEnsClaB, clauseType)).append(operationType)
					.append(joinClause(reqOrEnsClaA, clauseType)).append(";");
		} else if (reqOrEnsClaB.size() > 0) {
			builder.append(clauseType).append(" ").append(joinClause(reqOrEnsClaB, clauseType)).append(";");
		} else if (reqOrEnsClaA.size() > 0) {
			builder.append(clauseType).append(" ").append(joinClause(reqOrEnsClaA, clauseType)).append(";");
		}

		return builder.toString();
	}

	protected void plainContracting(final FSTTerminal terminalA, final FSTTerminal terminalB, final FSTTerminal terminalComp) {
		terminalComp.setBody(terminalB.getBody());
	}

	protected String replaceOriginal(final String[] baseCases, final String string, final int caseId, final String prefix) {
		String orig_repl = getOriginalReplacement(baseCases, caseId, prefix);
		if (orig_repl.isEmpty()) {
			// case: no original clause
			// TODO @Fabian is das richtig
			orig_repl = "true";
		}
		final String orig_case_repl = getOriginalCaseReplacement(baseCases, caseId);
		final String orig_spec_repl = getOriginalSpecReplacement(baseCases);
		return string.replace(CompositionConstants.ORIGINAL_KEYWORD_CLAUSE, orig_repl).replace(CompositionConstants.ORIGINAL_KEYWORD, orig_repl)
				.replace(CompositionConstants.ORIGINAL_SPEC_KEYWORD, orig_spec_repl).replace(CompositionConstants.ORIGINAL_CASE_KEYWORD, orig_case_repl);
	}

}
