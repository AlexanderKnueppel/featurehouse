package composer.rules.metaUseContracts;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import composer.CompositionException;
import composer.FSTGenComposerExtension;
import composer.rules.ContractComposition;
import composer.rules.meta.FeatureModelInfo;

import de.ovgu.cide.fstgen.ast.FSTNode;
import de.ovgu.cide.fstgen.ast.FSTNonTerminal;
import de.ovgu.cide.fstgen.ast.FSTTerminal;

/**
 * ContractComposition for metaproduct desgined to use contracts instead of method inlining during theorem proving
 * 
 * @author Stefan Krueger
 * @author Sebastian Krieter
 * 
 */
public class ContractCompositionMetaUseContracts extends ContractComposition {

	private static final String FM_FEATURE_MODEL = "FM.FeatureModel.";
	private static final String REQUIRE_OR_ORIGINAL = "FM.Features.OrOriginal";
	private static final String FINAL_CONTRACT = "requires FM.Contract.finalContract;";
	
	private static final Pattern p = Pattern.compile("(^|;)[^(requires|ensures|assignable)]*");
	private static final String marker = " ### ";
	private static final String domMarker = " ## ";
	private static final String delimiter = ";\n";

	private FeatureModelInfo modelInfo;
	public ContractCompositionMetaUseContracts(String contract_style) {
		super(contract_style);
	}

	public ContractCompositionMetaUseContracts(String contract_style, FeatureModelInfo model) {	
		super(contract_style);
		this.modelInfo = model;
	}
	
	public void setFeatureModelInfo(FeatureModelInfo model){
		this.modelInfo = model;
	}

	/**
	 * Calculates the name of the feature-state for a given {@link FSTNode} below the feature-node (without "FeatureModel.")
	 * @param node the {@link FSTNOde}
	 * @return name of the selection-state of the feature 
	 */
	private static String getFeatureState(FSTNode node) {
		return getFeatureName(node).toLowerCase() + (FSTGenComposerExtension.key ? "" : "()");
	}
	
	/**
	 * Returns the name of the Feature for a {@link FSTNode} below the feature node
	 * @param node the {@link FSTNode}
	 * @return name of the Feature
	 */
	private static String getFeatureName(FSTNode node) {
		if ("Feature".equals(node.getType()))
			return node.getName();
		else
			return getFeatureName(node.getParent());
	}
	
	/**
	 * Removes clause with disjunction of selection states from specification body
	 * @param body specification body
	 * @return specification body without disjunction of selection states
	 */
	private String removeRequireOrOriginal(String body){
		return body.replaceAll("requires FM.FeatureModel.[\\w]+" + (FSTGenComposerExtension.key ? "" : "\\(\\)") +" \\|\\| " + REQUIRE_OR_ORIGINAL + ";","");
	}
	
	private int aggregateClauses(StringBuilder clause, String[] contracts, int i, String line) {
		if (clause.length() > 0) {
			clause.append(" && ");
		}
		clause.append("(");
		clause.append(line.substring(line.indexOf(" ") + 1));
		while (!line.endsWith(";")) {
			line = contracts[++i].replace("@", "").trim();
			clause.append(line);
		}

		clause.append(")");
		return i;
	}

	private String transformIntoAbstractContract(FSTTerminal contract, boolean dispatch) {
		String contractBody = contract.getBody();
		StringBuilder ensures = new StringBuilder(), requires = new StringBuilder(), assignable = new StringBuilder();
		String[] contracts = contractBody.split("\n");
		for (int i = 0; i < contracts.length; i++) {
			String line = contracts[i].replace("@", "").trim();
			if (line.startsWith("requires")) {
				i = aggregateClauses(requires, contracts, i, line);
			} else if (line.startsWith("ensures")) {
				i = aggregateClauses(ensures, contracts, i, line);
			} else if (line.startsWith("assignable")) {
				assignable.append(line.replace("assignable", ""));
			}
		}

		String methodName = contract.getParent().getParent().getParent().getName();
		String placeholderName = !methodName.contains("(") ? methodName : ((dispatch) ? "dispatch_" : "") + methodName.substring(0, methodName.indexOf("("))
				+ "_" + contract.getOriginalFeatureName();
		StringBuilder ret = new StringBuilder("");
		ret.append("\t requires_abs ");
		ret.append(placeholderName);
		ret.append("R;\n\t def ");
		ret.append(placeholderName);
		ret.append("R = ");
		ret.append((requires.length() != 0) ? requires.toString().replace(";", "") + delimiter : ("true" + delimiter));
		ret.append("\t ensures_abs ");
		ret.append(placeholderName);
		ret.append("E;\n\t def ");
		ret.append(placeholderName);
		ret.append("E = ");
		ret.append((ensures.length() != 0) ? ensures.toString().replace(";", "") + delimiter : ("true" + delimiter));
		ret.append("\t assignable_abs ");
		ret.append(placeholderName);
		ret.append("A;\n\t def ");
		ret.append(placeholderName);
		ret.append("A = ");
		ret.append((assignable.length() != 0) ? assignable.toString() + "\n" : "\\everything\n");
		//ret.append("\t@");

		return ret.toString();
	}

	@Override
	public void compose(FSTTerminal terminalA, FSTTerminal terminalB, FSTTerminal terminalComp, FSTNonTerminal nonterminalParent) throws CompositionException {
		terminalA.setBody(terminalA.getBody().replace("\\not_composed\r\n", ""));
		String domBody = terminalA.getBody();
		final boolean first = terminalB.getBody().startsWith("\\not_composed\r\n");
		String oldDisp, oldDom = null;
		
		if (first) {
			terminalB.setBody(terminalB.getBody().replace("\\not_composed\r\n", ""));
			oldDisp = terminalB.getBody();
			oldDom = oldDisp;
		} else {
			String[] bodies = terminalB.getBody().split(marker);
			if (bodies.length == 2) {
				oldDisp = bodies[1];
				oldDom = bodies[0];
				int lDMInd = oldDom.lastIndexOf(domMarker);
				if (lDMInd >= 0) {
					oldDom = oldDom.substring(lDMInd + domMarker.length());
				}
			} else {
				oldDisp = bodies[0];
				oldDom = "";
			}
		}

		final String impliesBFM = FM_FEATURE_MODEL + terminalB.getOriginalFeatureName().toLowerCase() + " ==> ";
		StringBuilder ensuresDom = new StringBuilder(), requiresDom = new StringBuilder();
		boolean reqDomAdd = false, ensDomAdd = false;

		if (oldDom != null) {
			Matcher m = p.matcher(oldDom);
			if (m.find()) {
				int start = m.end();
				while (m.find()) {
					int end = m.start();
					String line = oldDom.substring(start, end);
					if (line.startsWith("requires") && !line.toLowerCase().contains("fm.featuremodel." + terminalB.getOriginalFeatureName().toLowerCase())) {
						requiresDom.append(" (");
						requiresDom.append(line.substring("requires".length()));
						requiresDom.append(")");
						requiresDom.append(" && ");
						reqDomAdd = true;
					} else if (line.startsWith("ensures")) {
						ensuresDom.append(" (");
						ensuresDom.append(line.substring("ensures".length()));
						ensuresDom.append(")");
						ensuresDom.append(" && ");
						ensDomAdd = true;
					}
					start = m.end();
				}
				if (reqDomAdd) {
					requiresDom.delete(requiresDom.length() - " && ".length(), requiresDom.length());
				}
				if (ensDomAdd) {
					ensuresDom.delete(ensuresDom.length() - " && ".length(), ensuresDom.length());
				}
			}
		}

		//terminalA => domBody
		Matcher m = p.matcher(oldDisp);
		Set<String> locSet = new HashSet<>();
		StringBuilder ensuresDisp = new StringBuilder(), requiresDisp = new StringBuilder();
		boolean reqAdd = false, ensAdd = false;
		String featureReq = FM_FEATURE_MODEL + terminalB.getOriginalFeatureName().toLowerCase() + " || " + REQUIRE_OR_ORIGINAL;
		if (m.find()) {
			int start = m.end();
			while (m.find()) {
				int end = m.start();
				String line = oldDisp.substring(start, end);
				if (line.startsWith("requires")) {
					if (line.contains(REQUIRE_OR_ORIGINAL)) {
						featureReq = line.substring("requires".length());				
					} else {
						requiresDisp.append(" (");
						requiresDisp.append(line.substring("requires".length()));
						requiresDisp.append(")");
						requiresDisp.append(" && ");
						reqAdd = true;
					}
				} else if (line.startsWith("ensures")) {
					ensuresDisp.append(" (");
					ensuresDisp.append(line.substring("ensures".length()));
					ensuresDisp.append(")");
					ensuresDisp.append(" && ");
					ensAdd = true;
				} else if (line.startsWith("assignable")) {
					Collections.addAll(locSet, line.substring("assignable".length()).replace(" ", "").split(","));
				}
				start = m.end();

			}
			if (reqAdd) {
				requiresDisp.delete(requiresDisp.length() - " && ".length(), requiresDisp.length());
			}
			if (ensAdd) {
				ensuresDisp.delete(ensuresDisp.length() - " && ".length(), ensuresDisp.length());
			}
		}

		StringBuilder contractBody = new StringBuilder();
		StringBuilder dispContractBody = new StringBuilder();
		m = p.matcher(domBody);

		if (m.find()) {
			final String impliesFM = FM_FEATURE_MODEL + terminalA.getOriginalFeatureName().toLowerCase() + " ==> ";
			int start = m.end();

			while (m.find()) {
				final int end = m.start();
				final String line = domBody.substring(start, end);
				final boolean origA = line.contains(ORIGINAL_KEYWORD);
				if (line.startsWith("requires")) {
					final String origDomRep = origA ? line.replace(ORIGINAL_KEYWORD, (reqDomAdd) ? requiresDom.toString() : " true") : line;
					contractBody.append(origDomRep);
					contractBody.append(delimiter);
					final int reqOrInd = line.lastIndexOf(REQUIRE_OR_ORIGINAL);
					if (reqOrInd >= 0) {
						dispContractBody.append(line.substring(0, reqOrInd) + featureReq);
					} else {
						final String origRep = origA ? line.replace(ORIGINAL_KEYWORD, (reqAdd) ? requiresDisp.toString() : " true") : line;
						dispContractBody.append("requires ");

						if (first && origA && !modelInfo.isCoreFeature(getFeatureName(terminalB))) {
							dispContractBody.append(impliesBFM);
						} else if (!origA)
							dispContractBody.append(impliesFM);
						dispContractBody.append(origRep.substring("requires ".length()));
					}
					dispContractBody.append(delimiter);
				} else if (line.startsWith("ensures")) {
					final String origRep = origA ? line.replace(ORIGINAL_KEYWORD, (ensAdd) ? ensuresDisp.toString() : " true") : line;
					final String origDomRep = origA ? line.replace(ORIGINAL_KEYWORD, (ensDomAdd) ? ensuresDom.toString() : " true") : line;
					contractBody.append(origDomRep);
					contractBody.append(delimiter);
					dispContractBody.append("ensures ");
					if (first && origA && !modelInfo.isCoreFeature(getFeatureName(terminalB))) {
						dispContractBody.append(impliesBFM);
					} else if (!origA)
						dispContractBody.append(impliesFM);
					dispContractBody.append(origRep.substring("ensures ".length()));
					dispContractBody.append(delimiter);
				} else if (line.startsWith("assignable")) {
					Collections.addAll(locSet, line.substring("assignable".length()).replace(" ", "").split(",\\s*"));
				}
				start = m.end();
			}
		}

		if (locSet.contains("\\everything")) {
			locSet.clear();
			locSet.add("\\everything");
		} else if (locSet.size() != 1) {
			locSet.remove("\\nothing");
		}

		if (!locSet.isEmpty()) {
			StringBuilder assignable = new StringBuilder("assignable ");
			for (String el : locSet) {
				if (!el.trim().isEmpty()) {
					assignable.append(el);
					assignable.append(",");
				}
			}
			String assignableC = assignable.toString().substring(0, assignable.length() - 1);
			contractBody.append(assignableC + ";");
			dispContractBody.append(assignableC + ";");
		}

		String dispBody = dispContractBody.toString();
		domBody = contractBody.toString();
		if (first) {
			domBody = "requires " + FM_FEATURE_MODEL + terminalB.getOriginalFeatureName().toLowerCase() + delimiter +
					oldDisp + domMarker + terminalB.getOriginalFeatureName() + domMarker + domBody;
		}

		terminalComp.setBody(domBody + marker + dispBody);
	}

	@Override
	public void preCompose(FSTTerminal terminal) {

		String body = terminal.getBody();
		if (modelInfo.isCoreFeature(getFeatureName(terminal)))
			terminal.setBody("\\not_composed\r\n\t" + body);
		else
			terminal.setBody("\\not_composed\r\n\trequires FM.FeatureModel." + getFeatureState(terminal) + " || " + REQUIRE_OR_ORIGINAL + ";\r\n\t" + body);
		return;
	}

	@Override
	public void postCompose(FSTTerminal terminal) {
		String body = terminal.getBody();
		if (removeRequireOrOriginal(body).trim().isEmpty()) {
			terminal.setBody("");
			return;
		}
		if (FSTGenComposerExtension.key && body.replaceAll("@", "").trim().isEmpty()) {
			return;
		}

		FSTNonTerminal nonT = (FSTNonTerminal) terminal.getParent().getParent().getParent();
		final FSTTerminal fstTerminal = (FSTTerminal) nonT.getChildren().get(2);
		String fstTBody = fstTerminal.getBody();
		final int ind = fstTBody.indexOf("{") + 1;

		if (fstTBody.charAt(ind) == '$') {
			//dispatch
			String[] bodies = terminal.getBody().split(marker);
			body = bodies.length == 2 ? bodies[1] : bodies[0];
			terminal.setBody(body);
			body = transformIntoAbstractContract(terminal, true);
		} else {
			//domain
			if (body.contains(marker)) {
				String[] bodies = terminal.getBody().split(marker);
				String domain = bodies[0];
				String[] domainCor = domain.split(domMarker);
				body = domainCor[domainCor.length == 3 ? ((domainCor[1].equals(fstTerminal.getOriginalFeatureName())) ? 0 : 2) : 0];
			} else {
				final String reqFeatName = "requires " + FM_FEATURE_MODEL + terminal.getOriginalFeatureName().toLowerCase();
				if (!body.contains(reqFeatName)) {
					body = reqFeatName + delimiter + body;
				}
			}
			terminal.setBody(body);
			
			body = transformIntoAbstractContract(terminal, false);
		}

		body = body.replaceAll(" \\|\\| " + REQUIRE_OR_ORIGINAL, "");
		body = body.replaceAll(FINAL_CONTRACT, "");
		body = body.replaceAll("requires  \\|\\| ", "");
		body = body.replaceAll("\\" + ORIGINAL_KEYWORD, "true");
		body = body.replaceAll("\\\\not_composed", "");

		terminal.setBody(body);

		body = terminal.getBody();

		while (body.contains("  "))
			body = body.replaceAll("  ", " ");

		while (body.contains("\r\n\t\r\n\t") || body.contains("\r\n\t \r\n\t"))
			body = body.replaceAll("\r\n[\\s]*\r\n\t", "\r\n\t");

		body = body.replaceAll("\r\n\t([\\w])", "\r\n\t $1");
		body = body.replaceAll("\r\n\t([\\s]*)", "\r\n\t  @$1");

		if (!body.endsWith("\r\n\t ")) {
			body = body + "\r\n\t ";
		}
		terminal.setBody(body);
	}

}