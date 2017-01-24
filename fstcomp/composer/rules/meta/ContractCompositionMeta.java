package composer.rules.meta;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import metadata.CompositionMetadataStore;

import composer.CompositionConstants;
import composer.CompositionException;
import composer.FSTGenComposerExtension;
import composer.rules.CompositionKeyword;
import composer.rules.ContractComposition;

import de.ovgu.cide.fstgen.ast.FSTNode;
import de.ovgu.cide.fstgen.ast.FSTNonTerminal;
import de.ovgu.cide.fstgen.ast.FSTTerminal;

/**
 * Contract Composition for Meta Product
 * 
 * @author Jens Meinicke
 * @author Matthias Praast
 * 
 */
//XXX Dots (.) need to be escaped in regexes
public class ContractCompositionMeta extends ContractComposition {

	private final CompositionMetadataStore metadata = CompositionMetadataStore.getInstance();
	private FeatureModelInfo modelInfo;
	
	public ContractCompositionMeta(final String contract_style) {
		super(contract_style);
	}

	public ContractCompositionMeta(final String contract_style, final FeatureModelInfo model) {
		super(contract_style);
		modelInfo = model;
	}

	/**
	 * Returns the name of the Feature for a {@link FSTNode} below the feature node
	 * 
	 * @param node the {@link FSTNode}
	 * @return name of the Feature
	 */
	private static String getFeatureName(final FSTNode node) {
		if ("Feature".equals(node.getType())) {
			return node.getName();
		} else {
			return getFeatureName(node.getParent());
		}
	}

	/**
	 * Calculates the name of the feature-state for a given {@link FSTNode} below the feature-node (without "FeatureModel.")
	 * 
	 * @param node the {@link FSTNOde}
	 * @return name of the selection-state of the feature
	 */
	private static String getFeatureState(final FSTNode node) {
		return getFeatureName(node).toLowerCase() + (FSTGenComposerExtension.key ? "" : "()");
	}

	@Override
	public void compose(final FSTTerminal terminalA, FSTTerminal terminalB, final FSTTerminal terminalComp, final FSTNonTerminal nonterminalParent)
			throws CompositionException {

		// compose the first specification with an empty one 
		if (terminalB.getBody().contains("\\not_composed\r\n")) {
			final FSTTerminal newComp = (FSTTerminal) terminalB.getDeepClone();
			final FSTTerminal newB = (FSTTerminal) terminalB.getDeepClone();
			newComp.setParent(terminalB.getParent());
			newB.setParent(terminalB.getParent());
			if (modelInfo.isCoreFeature(getFeatureName(terminalB))) {
				newB.setBody(contractStyle.equals(CompositionConstants.METHOD_BASED_COMPOSITION) ? "\r\n\trequires " + CompositionConstants.COMPOSITION_EXPLICIT + "();" : "");
			} else {
				newB.setBody("\r\n\trequires " + CompositionConstants.REQUIRE_OR_ORIGINAL + ";"
						+ (contractStyle.equals(CompositionConstants.METHOD_BASED_COMPOSITION) ? "\r\n\trequires " + CompositionConstants.COMPOSITION_EXPLICIT + "();" : ""));
			}
			compose(terminalB, newB, newComp, nonterminalParent);
			terminalB = newComp;
		}

		String body = terminalA.getBody();
		body = body.replaceAll("\\\\not_composed\r\n", "");
		terminalA.setBody(removeRequireOrOriginal(body));
		super.compose(terminalA, terminalB, terminalComp, nonterminalParent);
		terminalA.setBody(body);
	}

	@Override
	public void postCompose(final FSTTerminal terminal) {
		String body = terminal.getBody();
		if (removeRequireOrOriginal(body).trim().isEmpty()) {
			terminal.setBody("");
			return;
		}

		if (FSTGenComposerExtension.key && body.replaceAll("@", "").trim().isEmpty()) {
			return;
		}

		body = body.replaceAll(" \\|\\| " + CompositionConstants.REQUIRE_OR_ORIGINAL, "");
		body = body.replaceAll(CompositionConstants.FINAL_CONTRACT, "");
		body = body.replaceAll("requires  \\|\\| ", "");
		body = body.replaceAll("\\" + CompositionConstants.ORIGINAL_KEYWORD, "true");
		body = body.replaceAll("\\\\not_composed", "");
		if (FSTGenComposerExtension.key) {
			body = "  @ requires " + modelInfo.getValidClause() + ";\r\n\t" + body;
		} else {
			body = "  @ " + body;
		}

		terminal.setBody(body);

		if (contractStyle.equals(CompositionConstants.METHOD_BASED_COMPOSITION)) {
			postComposeMethodBased(terminal);
		}

		body = terminal.getBody();

		while (body.contains("  ")) {
			body = body.replaceAll("  ", " ");
		}

		while (body.contains("\r\n\t\r\n\t") || body.contains("\r\n\t \r\n\t")) {
			body = body.replaceAll("\r\n[\\s]*\r\n\t", "\r\n\t");
		}

		body = body.replaceAll("\r\n\t([\\w])", "\r\n\t $1");
		body = body.replaceAll("\r\n\t([\\s]*)", "\r\n\t  @$1");

		if (!body.endsWith("\r\n\t ")) {
			body = body + "\r\n\t ";
		}
		terminal.setBody(body);
	}

	@Override
	public void preCompose(final FSTTerminal terminal) {

		final String body = terminal.getBody();
		if (modelInfo.isCoreFeature(getFeatureName(terminal))) {
			terminal.setBody("\\not_composed\r\n\t" + body);
		} else {
			terminal.setBody("\\not_composed\r\n\trequires FM.FeatureModel." + getFeatureState(terminal) + " || " + CompositionConstants.REQUIRE_OR_ORIGINAL + ";\r\n\t" + body);
		}
		return;
	}

	public void setFeatureModelInfo(final FeatureModelInfo model) {
		modelInfo = model;
	}

	protected void composeByKey(final FSTTerminal terminalA, final FSTTerminal terminalB, final FSTTerminal terminalComp, final String compMethod) {
		if (compMethod.equals(CompositionConstants.COMPOSITION_CONJUNCTIVE)) {
			conjunctiveContracting(terminalA, terminalB, terminalComp);
		} else if (compMethod.equals(CompositionConstants.COMPOSITION_CONSECUTIVE)) {
			consecutiveContracting(terminalA, terminalB, terminalComp);
		} else if (compMethod.equals(CompositionConstants.COMPOSITION_CUMULATIVE)) {
			cumulativeContracting(terminalA, terminalB, terminalComp);
		} else if (compMethod.equals(CompositionConstants.COMPOSITION_PLAIN)) {
			plainContracting(terminalA, terminalB, terminalComp);
		} else if (compMethod.equals(CompositionConstants.COMPOSITION_EXPLICIT)) {
			explicitContracting(terminalA, terminalB, terminalComp);
		}

	}

	@Override
	protected void compositionByKeywords(final FSTTerminal terminalA, final FSTTerminal terminalB, final FSTTerminal terminalComp,
			final FSTNonTerminal nonterminalParent) {

		// first get all old Variants

		final HashMap<String, List<FSTTerminal>> variants = new HashMap<String, List<FSTTerminal>>();
		final List<FSTTerminal> reqClausesB = getRequiresClauses(terminalB);
		final List<FSTTerminal> ensClausesB = getEnsuresClauses(terminalB);
		final String bodyA = terminalA.getBody();

		addClausesToHashMap(reqClausesB, variants);
		addClausesToHashMap(ensClausesB, variants);

		final FeatureModelInfo originalModelInfo = modelInfo;
		modelInfo = new MethodBasedModelInfoWrapper(originalModelInfo);

		final FSTTerminal variantB = (FSTTerminal) terminalB.getDeepClone();
		variantB.setParent(terminalB.getParent());
		final FSTTerminal variantComp = (FSTTerminal) terminalComp.getDeepClone();
		variantComp.setParent(terminalComp.getParent());

		String newReqOrOriginal = "";
		String compRequires = "";
		String compEnsures = "";

		final String featureName = getFeatureName(terminalA);
		final String featureState = getFeatureState(terminalA);

		final boolean obligatory = originalModelInfo.isMethodCoreFeature(getClassName(terminalA), getMethodName(terminalA), featureName);

		for (final Map.Entry<String, List<FSTTerminal>> variantEntry : variants.entrySet()) {
			if (variantEntry.getKey().contains(CompositionConstants.REQUIRE_OR_ORIGINAL)) {
				if (!originalModelInfo.isCoreFeature(featureName)) {
					newReqOrOriginal = getNewReqOrOriginal(variantEntry.getValue().get(0).getBody(), getFeatureState(terminalA));
				}
				continue;
			}
			final String[] compInfo = extractCompositionInformation(variantEntry.getKey());
			final String[] oldBodyStrings = clauseListToStrings(variantEntry.getValue());
			setSelectedRejectedFromCompInfo((MethodBasedModelInfoWrapper) modelInfo, compInfo);
			if (newCompMethod(compInfo, terminalA)) {
				// new Compositions-Method -> FeatureState must be inserted into compInfo
				// 1. Feature not selected:
				if (!obligatory && modelInfo.canBeEliminated(featureName)) {
					compRequires += "\r\n\trequires " + compInfo[0] + "(!" + featureState + (compInfo[1].isEmpty() ? "" : "," + compInfo[1]) + ");\r\n\t"
							+ oldBodyStrings[0];
					compEnsures += "\r\n\tensures " + compInfo[0] + "(!" + featureState + (compInfo[1].isEmpty() ? "" : "," + compInfo[1]) + ");\r\n\t"
							+ oldBodyStrings[1];
				}
				// 2. Feature selected
				if (modelInfo.canBeSelected(featureName)) {
					// Compose with old method
					variantB.setBody(oldBodyStrings[0] + oldBodyStrings[1].trim());
					variantComp.setBody("");
					((MethodBasedModelInfoWrapper) modelInfo).setSelected(featureName);
					composeByKey(terminalA, variantB, variantComp, compInfo[0]);
					terminalA.setBody(bodyA);

					if (variantComp.getBody().trim().isEmpty()) {
						continue;
					}

					// write new Composition-Method
					final String compMethod = getCompMethodForTerminal(terminalA);
					compRequires += "\r\n\trequires " + compMethod + "(" + featureState + (compInfo[1].isEmpty() ? "" : "," + compInfo[1]) + ");";
					compEnsures += "\r\n\tensures " + compMethod + "(" + featureState + (compInfo[1].isEmpty() ? "" : "," + compInfo[1]) + ");";

					// write new Clauses
					final List<FSTTerminal> reqClausesComp = getRequiresClauses(variantComp);
					final List<FSTTerminal> ensClausesComp = getEnsuresClauses(variantComp);
					for (final FSTTerminal clause : reqClausesComp) {
						compRequires += "\r\n\t" + clause.getBody() + ";";
					}
					for (final FSTTerminal clause : ensClausesComp) {
						compEnsures += "\r\n\t" + clause.getBody() + ";";
					}
				}
			} else {
				// no new Coposition-Method
				// only add, when Feature can be selected, otherwise ignore
				if (modelInfo.canBeSelected(featureName)) {
					// call composition
					variantB.setBody(oldBodyStrings[0] + oldBodyStrings[1].trim());
					variantComp.setBody("");
					composeByKey(terminalA, variantB, variantComp, compInfo[0]);
					terminalA.setBody(bodyA);

					if (variantComp.getBody().trim().isEmpty()) {
						continue;
					}

					// write compostion-Method to Result
					compRequires += "\r\n\trequires " + compInfo[0] + "(" + compInfo[1] + ");";
					compEnsures += "\r\n\tensures " + compInfo[0] + "(" + compInfo[1] + ");";

					// Add new Clauses to result
					final List<FSTTerminal> reqClausesComp = getRequiresClauses(variantComp);
					final List<FSTTerminal> ensClausesComp = getEnsuresClauses(variantComp);
					for (final FSTTerminal clause : reqClausesComp) {
						compRequires += "\r\n\t" + clause.getBody() + ";";
					}
					for (final FSTTerminal clause : ensClausesComp) {
						compEnsures += "\r\n\t" + clause.getBody() + ";";
					}
				}
			}
		}

		terminalComp.setBody(newReqOrOriginal + "\r\n\t" + compRequires + "\r\n\t" + compEnsures);
		modelInfo = originalModelInfo;
	}

	@Override
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
		String terminalCompBody = "";
		String preClause = "";
		String postClause = "";
		final String featureState = getFeatureState(terminalA);

		if (!modelInfo.isMethodCoreFeature(getClassName(terminalA), getMethodName(terminalA), getFeatureName(terminalA))) {
			preClause = "FM.FeatureModel." + featureState + " ==> (";
			postClause = ")";
		}

		for (final FSTTerminal requiresB : reqClaB) {
			final String clauseBody = requiresB.getBody();
			if (clauseBody.contains(CompositionConstants.REQUIRE_OR_ORIGINAL)) {
				if (!modelInfo.isCoreFeature(getFeatureName(terminalA))) {
					terminalCompBody += getNewReqOrOriginal(clauseBody, featureState);
				}
				continue;
			}
			terminalCompBody += "\r\n\t " + requiresB.getBody() + ";";
		}

		for (final FSTTerminal requiresA : reqClaA) {
			terminalCompBody += "\r\n\t requires " + preClause + requiresA.getBody().replaceAll("requires ", "") + postClause + ";";
		}

		for (final FSTTerminal ensuresB : ensClaB) {
			terminalCompBody += "\r\n\t " + ensuresB.getBody() + ";";
		}

		for (final FSTTerminal ensuresA : ensClaA) {
			terminalCompBody += "\r\n\t ensures " + preClause + ensuresA.getBody().replaceAll("ensures ", "") + postClause + ";";
		}

		terminalComp.setBody(terminalCompBody);

	}

	@Override
	protected void consecutiveContracting(final FSTTerminal terminalA, final FSTTerminal terminalB, final FSTTerminal terminalComp) {
		// remove also from Spezifications
		if (terminalA.getBody().contains("also")) {
			desugarAlso(terminalA);
		}
		if (terminalB.getBody().contains("also")) {
			desugarAlso(terminalB);
		}
		String terminalCompBody = "";
		final String featureStateA = getFeatureState(terminalA);
		String preRequires = "";
		String postRequires = "";
		String preEnsures = "";
		String postEnsures = "";

		// get all Clauses
		final List<FSTTerminal> reqClausesA = getRequiresClauses(terminalA, true);
		final List<FSTTerminal> reqClausesB = getRequiresClauses(terminalB, true);
		final List<FSTTerminal> ensClausesA = getEnsuresClauses(terminalA);
		final List<FSTTerminal> ensClausesB = getEnsuresClauses(terminalB);

		// Search for the REquires or original-Clause
		for (final FSTTerminal clause : reqClausesB) {
			String clauseBody = clause.getBody();
			clauseBody = clauseBody.substring(0, clauseBody.length() - 1);
			if (clauseBody.contains(CompositionConstants.REQUIRE_OR_ORIGINAL)) {
				if (!modelInfo.isCoreFeature(getFeatureName(terminalA))) {
					terminalCompBody = getNewReqOrOriginal(clauseBody, featureStateA);
				}
				reqClausesB.remove(clause);
				break;
			}
		}

		// build new Clauses: Requires = \original || (FM.FeatureModel.FeatureName && (new Clauses))
		final String terminalARequires = reqClausesA.size() > 0 ? joinClause(reqClausesA, "requires") : "";
		final String terminalBRequires = reqClausesB.size() > 0 ? joinClause(reqClausesB, "requires") : "";

		if (!terminalARequires.trim().isEmpty()) {
			preEnsures = terminalARequires + " ==> (";
			postEnsures = ")";
		}

		if (!modelInfo.isMethodCoreFeature(getClassName(terminalA), getMethodName(terminalA), getFeatureName(terminalA))) {
			preRequires = "(FM.FeatureModel." + featureStateA + " && ";
			postRequires = ")";
			if (preEnsures.isEmpty()) { // no requires
				preEnsures = "FM.FeatureModel." + featureStateA + " ==> (";
			} else {
				preEnsures = "(FM.FeatureModel." + featureStateA + " && \\old" + terminalARequires + ") ==> (";
			}
			postEnsures = ")";
		}

		if (!terminalARequires.trim().isEmpty() && !terminalBRequires.trim().isEmpty()) {
			terminalCompBody += "\r\n\t requires " + terminalBRequires + "\r\n\t\t || " + preRequires + terminalARequires + postRequires + ";";
		} else if (!terminalARequires.trim().isEmpty()) {
			terminalCompBody += "\r\n\t requires " + preRequires + terminalARequires + postRequires + ";";
		} else if (!terminalBRequires.trim().isEmpty()) {
			terminalCompBody += "\r\n\t requires " + terminalBRequires + ";";
		}

		for (final FSTTerminal ensuresB : ensClausesB) {
			terminalCompBody += "\r\n\t " + ensuresB.getBody() + ";";
		}

		for (final FSTTerminal ensuresA : ensClausesA) {
			terminalCompBody += "\r\n\t ensures " + preEnsures + ensuresA.getBody().replaceAll("ensures ", "") + postEnsures + ";";
		}

		terminalComp.setBody(terminalCompBody);

	}

	@Override
	protected void contractOverriding(final FSTTerminal terminalA, final FSTTerminal terminalB, final FSTTerminal terminalComp) {

		// special case of explicit Contracting
		// -> only no \original
		// maybe should be checked...

		explicitContracting(terminalA, terminalB, terminalComp);

	}

	@Override
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

		String terminalCompBody = "";
		String preRequires = "";
		String postRequires = "";
		String preEnsures = "";
		String postEnsures = "";
		final String featureState = getFeatureState(terminalA);

		// Search for the REquires or original-Clause
		for (final FSTTerminal clause : reqClaB) {
			final String clauseBody = clause.getBody();
			if (clauseBody.contains(CompositionConstants.REQUIRE_OR_ORIGINAL)) {
				if (!modelInfo.isCoreFeature(getFeatureName(terminalA))) {
					terminalCompBody = getNewReqOrOriginal(clauseBody, featureState);
				}
				reqClaB.remove(clause);
				break;
			}
		}

		final String requiresA = reqClaA.size() > 0 ? joinClause(reqClaA, "requires") : "";
		final String requiresB = reqClaB.size() > 0 ? joinClause(reqClaB, "requires") : "";

		if (!modelInfo.isMethodCoreFeature(getClassName(terminalA), getMethodName(terminalA), getFeatureName(terminalA))) {
			preRequires = "FM.FeatureModel." + featureState + " && ";
			postRequires = "";
			preEnsures = "FM.FeatureModel." + featureState + " ==> (";
			postEnsures = ")";
		}

		if (!requiresA.trim().isEmpty() && !requiresB.trim().isEmpty()) {
			terminalCompBody += "\r\n\t requires " + requiresB + "\r\n\t\t || (" + preRequires + requiresA + postRequires + ");";
		} else if (!requiresA.trim().isEmpty()) {
			terminalCompBody += "\r\n\t requires " + preRequires + requiresA + postRequires + ";";
		} else if (!requiresB.trim().isEmpty()) {
			terminalCompBody += "\r\n\t requires " + requiresB + ");";
		}

		for (final FSTTerminal ensuresB : ensClaB) {
			terminalCompBody += "\r\n\t " + ensuresB.getBody() + ";";
		}

		for (final FSTTerminal ensuresA : ensClaA) {
			terminalCompBody += "\r\n\t ensures " + preEnsures + ensuresA.getBody().replaceAll("ensures ", "") + postEnsures + ";";
		}

		terminalComp.setBody(terminalCompBody);
	}

	@Override
	protected void explicitContracting(final FSTTerminal terminalA, final FSTTerminal terminalB, final FSTTerminal terminalComp) {

		if (terminalA.getBody().contains("also")) {
			desugarAlso(terminalA);
		}
		if (terminalB.getBody().contains("also")) {
			desugarAlso(terminalB);
		}

		final List<FSTTerminal> reqClausesA = getRequiresClauses(terminalA);
		final List<FSTTerminal> reqClausesB = getRequiresClauses(terminalB);
		final List<FSTTerminal> ensClausesA = getEnsuresClauses(terminalA);
		final List<FSTTerminal> ensClausesB = getEnsuresClauses(terminalB);

		final String featureState = getFeatureState(terminalA);
		final String methodName = getMethodName(terminalA);
		final boolean isObligatory = modelInfo.isMethodCoreFeature(getClassName(terminalA), methodName, getFeatureName(terminalA));

		String bodyComp = "";

		for (final FSTTerminal clause : reqClausesB) {
			final String clauseBody = clause.getBody();
			if (clauseBody.contains(CompositionConstants.REQUIRE_OR_ORIGINAL)) {
				clause.setBody("");
				if (!modelInfo.isCoreFeature(getFeatureName(terminalA))) {
					bodyComp += getNewReqOrOriginal(clauseBody, featureState);
				}
				break;
			}
		}

		bodyComp += explicitComposeClauses(reqClausesB, reqClausesA, terminalB, "requires", featureState, isObligatory);

		bodyComp += explicitComposeClauses(ensClausesB, ensClausesA, terminalB, "ensures", featureState, isObligatory);

		bodyComp = bodyComp.replace(CompositionConstants.ORIGINAL_CALL, methodName + "__wrappee__" + terminalB.getOriginalFeatureName() + "(");

		terminalComp.setBody(bodyComp);
	}

	// Changed to get Clauses without Semicolon, skip super-call if empty body (otherwise would get an error)
	@Override
	protected List<FSTTerminal> getEnsuresClauses(final FSTTerminal terminal) {
		return getEnsuresClauses(terminal, false);
	}

	protected List<FSTTerminal> getEnsuresClauses(final FSTTerminal terminal, final boolean keepSemi) {
		if (terminal.getBody().replaceAll("\r", "").replaceAll("\n", "").replaceAll("\t", "").trim().isEmpty()) {
			return new ArrayList<FSTTerminal>();
		}
		final List<FSTTerminal> clauses = super.getEnsuresClauses(terminal);
		if (keepSemi) {
			return clauses;
		}
		for (final FSTTerminal clause : clauses) {
			clause.setBody(clause.getBody().substring(0, clause.getBody().length() - 1));
		}
		return clauses;
	}

	// Changed to get Clauses without Semicolon, skip super-call if empty body (otherwise would get an error)
	@Override
	protected List<FSTTerminal> getRequiresClauses(final FSTTerminal terminal) {
		return getRequiresClauses(terminal, false);
	}

	protected List<FSTTerminal> getRequiresClauses(final FSTTerminal terminal, final boolean keepSemi) {
		if (terminal.getBody().replaceAll("\r", "").replaceAll("\n", "").replaceAll("\t", "").trim().isEmpty()) {
			return new ArrayList<FSTTerminal>();
		}
		final List<FSTTerminal> clauses = super.getRequiresClauses(terminal);
		if (keepSemi) {
			return clauses;
		}
		for (final FSTTerminal clause : clauses) {
			clause.setBody(clause.getBody().substring(0, clause.getBody().length() - 1));
		}
		return clauses;

	}

	@Override
	protected void plainContracting(final FSTTerminal terminalA, final FSTTerminal terminalB, final FSTTerminal terminalComp) {
		final List<FSTTerminal> reqClausesB = getRequiresClauses(terminalB);
		String newOrOriginal = "";
		String oldOrOriginal = "";
		final String featureName = getFeatureName(terminalA);
		for (final FSTTerminal clause : reqClausesB) {
			if (clause.getBody().contains(CompositionConstants.REQUIRE_OR_ORIGINAL)) {
				if (!modelInfo.isCoreFeature(featureName)) {
					oldOrOriginal = clause.getBody();
					newOrOriginal = getNewReqOrOriginal(clause.getBody(), getFeatureState(terminalA));
				}
				break;
			}
		}

		final String bodyB = terminalB.getBody();
		if (bodyB.contains(CompositionConstants.FINAL_CONTRACT)) {
			terminalComp.setBody(bodyB.replace(oldOrOriginal, newOrOriginal));
			return;
		}

		final boolean isObligatory = modelInfo.isMethodCoreFeature(getClassName(terminalA), getMethodName(terminalA), featureName);

		if (isObligatory && terminalB.getBody().trim().isEmpty()) {
			if (!modelInfo.isCoreFeature(featureName)) {
				terminalComp.setBody(newOrOriginal + "\r\n\t " + terminalA.getBody() + CompositionConstants.FINAL_CONTRACT);
			} else {
				terminalComp.setBody(terminalA.getBody() + CompositionConstants.FINAL_CONTRACT);
			}
			return;
		}

		final List<FSTTerminal> reqClausesA = getRequiresClauses(terminalA);
		final List<FSTTerminal> ensClausesA = getEnsuresClauses(terminalA);
		final List<FSTTerminal> ensClausesB = getEnsuresClauses(terminalB);

		String bodyComp = CompositionConstants.FINAL_CONTRACT;
		String pre = "";
		String post = "";
		if (!isObligatory) {
			bodyComp = "";
			pre = "FM.FeatureModel." + getFeatureState(terminalA) + " ==> (";
			post = ")";
		}

		final Set<String> features = getFeatures(reqClausesB, "requires");
		features.addAll(getFeatures(ensClausesB, "ensures"));

		for (final String feature : features) {
			pre += "!FM.FeatureModel." + feature + " ==> (";
			post += ")";
		}

		for (final FSTTerminal clause : reqClausesB) {
			if (clause.getBody().contains(CompositionConstants.REQUIRE_OR_ORIGINAL)) {
				if (!modelInfo.isCoreFeature(featureName)) {
					bodyComp += newOrOriginal;
				}
				continue;
			}
			bodyComp += "\r\n\t " + clause.getBody() + ";";
		}

		for (final FSTTerminal clause : reqClausesA) {
			bodyComp += "\r\n\t requires " + pre + clause.getBody().replaceAll("requires ", "") + post + ";";
		}

		for (final FSTTerminal clause : ensClausesB) {
			bodyComp += "\r\n\t " + clause.getBody() + ";";
		}

		for (final FSTTerminal clause : ensClausesA) {
			bodyComp += "\r\n\t ensures " + pre + clause.getBody().replaceAll("ensures ", "") + post + ";";
		}

		terminalComp.setBody(bodyComp);

	}

	/**
	 * Adds Clauses to a Hash-Map. Hash-Map maps from composition information string to according clauses
	 * 
	 * @param clauses clauses to add
	 * @param hashMap HashMap to add clauses to
	 */
	private void addClausesToHashMap(final List<FSTTerminal> clauses, final HashMap<String, List<FSTTerminal>> hashMap) {
		List<FSTTerminal> currentEntry = null;
		for (final FSTTerminal clause : clauses) {
			final String clauseBody = clause.getBody();
			if (clauseBody.contains(CompositionConstants.REQUIRE_OR_ORIGINAL)) {
				final LinkedList<FSTTerminal> reqOrOriginal = new LinkedList<FSTTerminal>();
				reqOrOriginal.add(clause);
				hashMap.put(CompositionConstants.REQUIRE_OR_ORIGINAL, reqOrOriginal);
				continue;
			}
			if (clauseBody.contains(CompositionConstants.COMPOSITION_CONJUNCTIVE) || clauseBody.contains(CompositionConstants.COMPOSITION_CONSECUTIVE) || clauseBody.contains(CompositionConstants.COMPOSITION_CUMULATIVE)
					|| clauseBody.contains(CompositionConstants.COMPOSITION_EXPLICIT) || clauseBody.contains(CompositionConstants.COMPOSITION_PLAIN)) {
				//currentEntry = null;
				currentEntry = hashMap.get(clauseBody.replaceAll("requires", "").replaceAll("ensures", "").trim());
				if (currentEntry == null) {
					currentEntry = new LinkedList<FSTTerminal>();
					hashMap.put(clauseBody.replaceAll("requires", "").replaceAll("ensures", "").trim(), currentEntry);
				}
				continue;
			}

			if (currentEntry == null) {
				// should not happen
				continue;
			}

			currentEntry.add(clause);
		}
	}

	/**
	 * writes clauses into a String-Array with length 2 (requires-clauses and ensures-clauses)
	 * 
	 * @param clauses to put into the Array
	 * @return String-Array (requires-clauses and ensures-clauses)
	 */
	private String[] clauseListToStrings(final List<FSTTerminal> clauses) {
		final String[] result = { "", "" };

		for (final FSTTerminal clause : clauses) {
			if (clause.getBody().contains(CompositionConstants.COMPOSITION_CONJUNCTIVE) || clause.getBody().contains(CompositionConstants.COMPOSITION_CONSECUTIVE)
					|| clause.getBody().contains(CompositionConstants.COMPOSITION_CUMULATIVE) || clause.getBody().contains(CompositionConstants.COMPOSITION_EXPLICIT)
					|| clause.getBody().contains(CompositionConstants.COMPOSITION_PLAIN)) {
				continue;
			}
			if (clause.getBody().contains(CompositionConstants.REQUIRE_OR_ORIGINAL)) {
				continue;
			}
			if (clause.getBody().contains("requires ")) {
				result[0] += clause.getBody() + ";\r\n\t";
			} else if (clause.getBody().contains("ensures ")) {
				result[1] += clause.getBody() + ";\r\n\t";
			}
		}

		return result;
	}

	private String explicitComposeClauses(final List<FSTTerminal> originalClauses, final List<FSTTerminal> newClauses, final FSTTerminal originalTerminal,
			final String type, final String featureState, final boolean isObligatory) {

		String result = "";
		String pre = "";
		String post = "";
		final boolean andOriginal = removeAndOriginal(newClauses, type);
		// only implication, when not extended (no "requires \original"; or similar)
		if (!andOriginal) {
			pre = "!FM.FeatureModel." + featureState + " ==> (";
			post = ")";

		}

		// skip original clauses if Feature is obligatory for the method
		// except: FeatureA is obligatory but extends the spezification
		if (!isObligatory || andOriginal) {
			for (final FSTTerminal clause : originalClauses) {
				if (clause.getBody().trim().isEmpty()) {
					continue;
				}
				final String newClause = "\r\n\t " + type + " " + pre + clause.getBody().replace(type + " ", "") + post + ";";
				// don't add Clause if feature-combination is not possible
				modelInfo.reset();
				selectFeaturesFromClause(newClause);
				rejectFeaturesFromClause(newClause);
				if (modelInfo.isValidSelection()) {
					result += simplifyImplications(newClause);
				}
			}
		}

		// always add new clauses
		// when not obligatory: with implications
		pre = "";
		post = "";
		if (!isObligatory) {
			pre = "FM.FeatureModel." + featureState + " ==> (";
			post = ")";
		}
		for (final FSTTerminal clause : newClauses) {
			if (clause.getBody().trim().isEmpty()) {
				continue;
			}
			result += "\r\n\t " + type + " " + pre;

			final String clauseBody = clause.getBody();

			if (clauseBody.contains(CompositionConstants.ORIGINAL_KEYWORD) || clauseBody.contains(CompositionConstants.ORIGINAL_KEYWORD_CLAUSE) || clauseBody.contains(CompositionConstants.ORIGINAL_CASE_KEYWORD)
					|| clauseBody.contains(CompositionConstants.ORIGINAL_SPEC_KEYWORD)) {
				result += replaceOriginal(
						new String[] { originalTerminal.getBody().replaceAll(
								"requires (FM.FeatureModel.[\\w]+\\(?\\)?)?( \\|\\| FM.FeatureModel.[\\w]+\\(?\\)?)*" + " \\|\\| " + CompositionConstants.REQUIRE_OR_ORIGINAL + ";",
								"") }, clauseBody, 0, type).replace(type + " ", "");
			} else {
				result += clauseBody.replace(type + " ", "");
			}

			result += post + ";";
		}

		return result;
	}

	/**
	 * Calculates informations for composition for method-based Contract Refinement
	 * 
	 * @param clause clause with compostions informatiuons (syntax: "&lt;composition-type&gt;(&lt;list of featurestates&gt;)" )
	 * @return String-Array with 4 elements: <br>
	 *         0 composition-type <br>
	 *         1 list of featurestates (&lt;featurestate1&gt;,...,&lt;featurestaten&gt;) <br>
	 *         2 resulting prefix in specification <br>
	 *         3 resulting suffix in specification
	 */
	private String[] extractCompositionInformation(final String clause) {
		final String[] result = { "", "", "", "" };
		final Pattern p = Pattern.compile("(" + "FM.CompositionConjunctive" + "|" + "FM.CompositionConsecutive" + "|" + "FM.CompositionCumulative" + "|"
				+ "FM.CompositionExplicit" + "|" + "FM.CompositionPlain" + ")\\(" + "((!?[\\w]+\\(?\\)?)?(,(!?[\\w]+\\(?\\)?))*)" + "\\)");
		final Matcher m = p.matcher(clause);
		if (m.find()) {
			result[0] = m.group(1);
			result[1] = m.group(2);
			for (final String status : result[1].split(",")) {
				if (status.isEmpty()) {
					continue;
				}
				if (status.charAt(0) == '!') {
					result[2] += "!FM.FeatureModel." + status.substring(1) + " ==> (";
				} else {
					result[2] += "FM.FeatureModel." + status + " ==> (";
				}
				result[3] += ")";
			}

		}

		return result;
	}

	/**
	 * Calculates informations for composition for method-based Contract Refinement
	 * 
	 * @param clause clause with compostions informatiuons (syntax: "&lt;clausetype&gt; &lt;composition-type&gt;(&lt;list of featurestates&gt;)" )
	 * @param type type of clauses ("requires" or "ensures")
	 * @return String-Array with 4 elements: <br>
	 *         0 composition-type <br>
	 *         1 list of featurestates (&lt;featurestate1&gt;,...,&lt;featurestaten&gt;) <br>
	 *         2 resulting prefix in specification <br>
	 *         3 resulting suffix in specification
	 */
	private String[] extractCompositionInformation(final String clause, final String type) {
		final String[] result = { "", "", "", "" };
		final Pattern p = Pattern.compile(type + " (" + CompositionConstants.COMPOSITION_CONJUNCTIVE + "|" + CompositionConstants.COMPOSITION_CONSECUTIVE + "|" + CompositionConstants.COMPOSITION_CUMULATIVE + "|"
				+ CompositionConstants.COMPOSITION_EXPLICIT + "|" + CompositionConstants.COMPOSITION_PLAIN + ")\\(" + "((!?[\\w]+\\(?\\)?)?(,(!?[\\w]+\\(?\\)?))*)" + "\\)");
		final Matcher m = p.matcher(clause);
		if (m.find()) {
			result[0] = m.group(1);
			result[1] = m.group(2);
			for (final String status : result[1].split(",")) {
				if (status.isEmpty()) {
					continue;
				}
				if (status.charAt(0) == '!') {
					result[2] += "!FM.FeatureModel." + status.substring(1) + " ==> (";
				} else {
					result[2] += "FM.FeatureModel." + status + " ==> (";
				}
				result[3] += ")";
			}
		}

		return result;
	}

	/**
	 * Determines the class name for a {@link FSTNode} of a method specification
	 * 
	 * @param node specification node
	 * @return class name
	 */
	private String getClassName(final FSTNode node) {
		if (node == null) {
			return "";
		}
		if (node.getType().contains("ClassDeclaration")) {
			return node.getName();
		}
		return getClassName(node.getParent());
	}

	private String getCompMethodByCompositionKey(final String compositionKey) {
		if (compositionKey.equals(CompositionKeyword.CONJUNCTIVE_CONTRACT.getLabel())) {
			return CompositionConstants.COMPOSITION_CONJUNCTIVE;
		}
		if (compositionKey.equals(CompositionKeyword.CONSECUTIVE_CONTRACT.getLabel())) {
			return CompositionConstants.COMPOSITION_CONSECUTIVE;
		}
		if (compositionKey.equals(CompositionKeyword.CUMULATIVE_CONTRACT.getLabel())) {
			return CompositionConstants.COMPOSITION_CUMULATIVE;
		}
		if (compositionKey.equals(CompositionKeyword.FINAL_CONTRACT.getLabel()) || compositionKey.equals(CompositionKeyword.FINAL_METHOD.getLabel())) {
			return CompositionConstants.COMPOSITION_PLAIN;
		}
		return CompositionConstants.COMPOSITION_EXPLICIT;
	}

	private String getCompMethodForTerminal(final FSTTerminal terminal) {
		final String compositionKey = getCompositionKey(terminal);
		if (compositionKey.equals(CompositionKeyword.CONJUNCTIVE_CONTRACT.getLabel())) {
			return CompositionConstants.COMPOSITION_CONJUNCTIVE;
		}
		if (compositionKey.equals(CompositionKeyword.CONSECUTIVE_CONTRACT.getLabel())) {
			return CompositionConstants.COMPOSITION_CONSECUTIVE;
		}
		if (compositionKey.equals(CompositionKeyword.CUMULATIVE_CONTRACT.getLabel())) {
			return CompositionConstants.COMPOSITION_CUMULATIVE;
		}
		if (compositionKey.equals(CompositionKeyword.FINAL_CONTRACT.getLabel()) || compositionKey.equals(CompositionKeyword.FINAL_METHOD.getLabel())) {
			return CompositionConstants.COMPOSITION_PLAIN;
		}
		if (compositionKey.equals(CompositionKeyword.EXPLICIT_CONTRACT.getLabel())) {
			return CompositionConstants.COMPOSITION_EXPLICIT;
		}
		return "";
	}

	/**
	 * Calculates the compositions-keyword for a {@link FSTNode} of a specification
	 * 
	 * @param terminal specification node
	 * @return composition-keyword
	 */
	private String getCompositionKey(final FSTTerminal terminal) {
		String compKey = "";
		for (final FSTNode n : terminal.getParent().getChildren()) {
			if (n.getType().equals("ContractCompKey")) {
				compKey = ((FSTTerminal) n).getContractCompKey();
				break;
			}
		}
		return compKey;
	}

	/**
	 * Calculates all selectionsstates of features that occur in the given clauses
	 * 
	 * @param clauses clauses to check for selectionsstates
	 * @param clauseType type of clauses ("requires" or "ensures")
	 * @return Set of selectionsstates of features
	 */
	private Set<String> getFeatures(final List<FSTTerminal> clauses, final String clauseType) {
		final HashSet<String> result = new HashSet<String>();

		final Pattern p = Pattern.compile(clauseType + " !?FM\\.FeatureModel\\.([\\w]+" + (FSTGenComposerExtension.key ? "" : "\\(\\)") + ") ==> \\(");

		for (final FSTTerminal clause : clauses) {
			String clauseBody = clause.getBody();
			Matcher m = p.matcher(clauseBody);
			while (m.find()) {
				result.add(m.group(1));
				clauseBody = clauseBody.replaceAll(p.pattern(), clauseType + " ");
				m = p.matcher(clauseBody);
			}
		}

		return result;
	}

	
	/**
	 * adds additional selection state to disjunction of features
	 * 
	 * @param oldRequiresClause old clause with disjunction of features
	 * @param featureState selectionstate to add
	 * @return new clause with added selectionstate
	 */
	private String getNewReqOrOriginal(final String oldRequiresClause, final String featureState) {
		//XXX Technically wrong because . means 'any character' in a regex. replaceAll uses regexs. To fix, use replace.
		final String clauseBody = oldRequiresClause.replaceAll(CompositionConstants.REQUIRE_OR_ORIGINAL, "FM.FeatureModel." + featureState + " || " + CompositionConstants.REQUIRE_OR_ORIGINAL);
		return clauseBody + ";";
	}

	private boolean newCompMethod(final String[] compInfo, final FSTTerminal terminal) {
		final String compKey = getCompositionKey(terminal);
		if (compKey.equals("")) {
			return false;
		}
		return !compInfo[0].equals(getCompMethodByCompositionKey(compKey));
	}

	private void postComposeMethodBased(final FSTTerminal terminal) {
		final List<FSTTerminal> reqClauses = getRequiresClauses(terminal);
		final List<FSTTerminal> ensClauses = getEnsuresClauses(terminal);

		final FeatureModelInfo originalModelInfo = modelInfo;

		modelInfo = new MethodBasedModelInfoWrapper(modelInfo);

		String[] currentCompInfo = { "", "", "", "" };
		String newBody = "";

		for (final FSTTerminal clause : reqClauses) {
			if (clause.getBody().contains(CompositionConstants.REQUIRE_OR_ORIGINAL)) {
				newBody += "\r\n\t" + clause.getBody() + ";";
				continue;
			}
			if (clause.getBody().contains(CompositionConstants.COMPOSITION_EXPLICIT)) {
				currentCompInfo = extractCompositionInformation(clause.getBody(), "requires");
				continue;
			}
			if (clause.getBody().contains(CompositionConstants.COMPOSITION_CONJUNCTIVE)) {
				currentCompInfo = extractCompositionInformation(clause.getBody(), "requires");
				continue;
			}
			if (clause.getBody().contains(CompositionConstants.COMPOSITION_CUMULATIVE)) {
				currentCompInfo = extractCompositionInformation(clause.getBody(), "requires");
				continue;
			}
			if (clause.getBody().contains(CompositionConstants.COMPOSITION_CONSECUTIVE)) {
				currentCompInfo = extractCompositionInformation(clause.getBody(), "requires");
				continue;
			}
			if (clause.getBody().contains(CompositionConstants.COMPOSITION_PLAIN)) {
				currentCompInfo = extractCompositionInformation(clause.getBody(), "requires");
				continue;
			}
			final String newClause = "requires " + currentCompInfo[2] + clause.getBody().replaceAll("requires ", "") + currentCompInfo[3] + ";";
			modelInfo.reset();
			selectFeaturesFromClause(newClause);
			rejectFeaturesFromClause(newClause);
			if (modelInfo.isValidSelection()) {
				newBody += "\r\n\t" + simplifyImplications(newClause);
			}
		}

		currentCompInfo[2] = "";
		currentCompInfo[3] = "";
		for (final FSTTerminal clause : ensClauses) {
			if (clause.getBody().contains(CompositionConstants.COMPOSITION_EXPLICIT)) {
				currentCompInfo = extractCompositionInformation(clause.getBody(), "ensures");
				continue;
			}
			if (clause.getBody().contains(CompositionConstants.COMPOSITION_CONJUNCTIVE)) {
				currentCompInfo = extractCompositionInformation(clause.getBody(), "ensures");
				continue;
			}
			if (clause.getBody().contains(CompositionConstants.COMPOSITION_CUMULATIVE)) {
				currentCompInfo = extractCompositionInformation(clause.getBody(), "ensures");
				continue;
			}
			if (clause.getBody().contains(CompositionConstants.COMPOSITION_CONSECUTIVE)) {
				currentCompInfo = extractCompositionInformation(clause.getBody(), "ensures");
				continue;
			}
			if (clause.getBody().contains(CompositionConstants.COMPOSITION_PLAIN)) {
				currentCompInfo = extractCompositionInformation(clause.getBody(), "ensures");
				continue;
			}
			final String newClause = "ensures " + currentCompInfo[2] + clause.getBody().replaceAll("ensures ", "") + currentCompInfo[3] + ";";
			modelInfo.reset();
			selectFeaturesFromClause(newClause);
			rejectFeaturesFromClause(newClause);
			if (modelInfo.isValidSelection()) {
				newBody += "\r\n\t" + simplifyImplications(newClause);
			}
		}
		modelInfo = originalModelInfo;

		terminal.setBody(newBody);
	}

	/**
	 * Unselects all features in modelInfo, that ar marked as unselected ( !FeatureModel.&lt;FeatureState&lt; )
	 * 
	 * @param clause clause with implications
	 */
	private void rejectFeaturesFromClause(final String clause) {
		final Pattern featurePattern = Pattern.compile("!FM\\.FeatureModel\\.([\\w]+)" + (FSTGenComposerExtension.key ? "" : "\\(\\)") + " ==>");
		final Matcher featureMatcher = featurePattern.matcher(clause);
		while (featureMatcher.find()) {
			modelInfo.eliminateFeature(stateToFeatureName(featureMatcher.group(1)));
		}
	}

	/**
	 * Calculates if original clauses must be fulfilled to fulfill new clauses. Removes original in that case
	 * 
	 * @param clauses clauses that may contain original
	 * @param clauseType type of clauses ("requires" or "ensures")
	 * @return true, if original clauses must be fulfilled
	 */
	private boolean removeAndOriginal(final List<FSTTerminal> clauses, final String clauseType) {
		boolean result = false;
		for (final FSTTerminal clause : clauses) {
			String body = clause.getBody();
			// skip the rest if /original is not in the clause
			if (!body.contains(CompositionConstants.ORIGINAL_KEYWORD)) {
				continue;
			}

			// find out, whether it is composend with an and:
			// Possibilities:
			//	1. requires \original;
			// 	2. requires \original && ...
			while (body.contains("  ")) {
				body = body.replaceAll("  ", " ");
			}

			// 1.
			if (body.trim().equals(clauseType + " " + CompositionConstants.ORIGINAL_KEYWORD)) {
				clause.setBody("");
				result = true;
			}

			// 2. (first delete all linefeeds, double spaces, tabs)
			body = body.replaceAll("\r", "").replaceAll("\n", "").replaceAll("\t", "");
			while (body.contains("  ")) {
				body = body.replaceAll("  ", " ");
			}

			final Pattern p = Pattern.compile(clauseType + "[\\s]+\\" + CompositionConstants.ORIGINAL_KEYWORD + "[\\s]+&&[\\s]+");
			final Matcher m = p.matcher(body);
			if (m.find()) {
				clause.setBody(clause.getBody().replaceAll(p.pattern(), clauseType + " "));
				result = true;
			}
		}
		return result;
	}

	/**
	 * Removes clause with disjunction of selection states from specification body
	 * 
	 * @param body specification body
	 * @return specification body without disjunction of selection states
	 */
	private String removeRequireOrOriginal(final String body) {
		return body.replaceAll("requires FM.FeatureModel.[\\w]+" + (FSTGenComposerExtension.key ? "" : "\\(\\)") + " \\|\\| " + CompositionConstants.REQUIRE_OR_ORIGINAL + ";", "");
	}

	/**
	 * Selects all features in modelInfo, that are marked as selected ( FeatureModel.&lt;FeatureState&lt; without leading !)
	 * 
	 * @param clause clause with implications
	 */
	private void selectFeaturesFromClause(final String clause) {
		final Pattern featurePattern = Pattern.compile("[^!]FM\\.FeatureModel\\.([\\w]+)" + (FSTGenComposerExtension.key ? "" : "\\(\\)") + " ==>");
		final Matcher featureMatcher = featurePattern.matcher(" " + clause);
		while (featureMatcher.find()) {
			modelInfo.selectFeature(stateToFeatureName(featureMatcher.group(1)));
		}
	}

	/**
	 * selects/unselects Features in a {@link FeatureModelInfo} from a composition information array
	 * 
	 * @param specialModelInfo object of {@link FeatureModelInfo} to select/unselect features
	 * @param compInfo composition information array
	 */
	private void setSelectedRejectedFromCompInfo(final MethodBasedModelInfoWrapper specialModelInfo, final String[] compInfo) {
		specialModelInfo.clear();
		if (compInfo == null) {
			return;
		}

		for (final String status : compInfo[1].split(",")) {
			if (status.isEmpty()) {
				continue;
			}
			if (status.charAt(0) == '!') {
				specialModelInfo.setRejected(stateToFeatureName(status.substring(1)));
			} else {
				specialModelInfo.setSelected(stateToFeatureName(status));
			}
		}
	}

	/**
	 * Simplifies Clauses. Removes implications if the selectionstate is already implied by an other selectionstate (or combination of selectionstates)
	 * 
	 * @param clause clause to simplify
	 * @return simplified clause
	 */
	private String simplifyImplications(final String clause) {
		String simplifiedClause = clause;
		final Pattern pat = Pattern.compile("FM\\.FeatureModel\\.([\\w]+)" + (FSTGenComposerExtension.key ? "" : "\\(\\)") + " ==>");
		final Matcher match = pat.matcher(clause);
		modelInfo.reset();
		while (match.find()) {
			final String featureName = stateToFeatureName(match.group(1));
			final char prefChar = match.start() > 0 ? clause.charAt(match.start() - 1) : ' ';
			if (prefChar == '!') {
				if (modelInfo.isAlwaysEliminated(featureName)) {
					simplifiedClause = simplifiedClause.replaceAll("!FM.FeatureModel." + match.group(1).replaceAll("\\(\\)", "") + "\\(?\\)? ==> ", "");
				} else {
					modelInfo.eliminateFeature(featureName);
				}
			} else {
				if (modelInfo.isAlwaysSelected(featureName)) {
					simplifiedClause = simplifiedClause.replaceAll("([^!])FM.FeatureModel." + match.group(1).replaceAll("\\(\\)", "") + "\\(?\\)? ==> ", "$1");
				} else {
					modelInfo.selectFeature(featureName);
				}
			}
		}

		return simplifiedClause;
	}

	/**
	 * Translates selectionstate of feature into feature-name.
	 * 
	 * @param state selectionsstate of Features
	 * @return name of Features
	 */
	private String stateToFeatureName(String state) {
		final List<String> features = metadata.getFeatures();
		state = state.replaceAll("()", "");
		for (final String feature : features) {
			if (feature.toLowerCase().equals(state)) {
				return feature;
			}
		}
		return state;
	}

}