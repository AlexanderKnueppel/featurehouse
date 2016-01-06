package composer.rules.metaUseContracts;

import static composer.CompositionConstants.AND_WS;
import static composer.CompositionConstants.ASSIGNABLE;
import static composer.CompositionConstants.COMMA;
import static composer.CompositionConstants.CONSTRUCTOR_CONCATENATION;
import static composer.CompositionConstants.DISPATCH;
import static composer.CompositionConstants.DISPATCH_;
import static composer.CompositionConstants.ENSURES;
import static composer.CompositionConstants.EVERYTHING;
import static composer.CompositionConstants.FINAL_CONTRACT;
import static composer.CompositionConstants.FM_MODEL;
import static composer.CompositionConstants.FST_METHOD_INDEX;
import static composer.CompositionConstants.IMPLICATION_WS;
import static composer.CompositionConstants.LBRACE;
import static composer.CompositionConstants.NEWLINE;
import static composer.CompositionConstants.NOTHING;
import static composer.CompositionConstants.NOT_COMPOSED;
import static composer.CompositionConstants.ORIGINAL_CALL;
import static composer.CompositionConstants.ORIGINAL_KEYWORD;
import static composer.CompositionConstants.OR_WS;
import static composer.CompositionConstants.RBRACE;
import static composer.CompositionConstants.REGEX_COMMA_WS;
import static composer.CompositionConstants.REQUIRES;
import static composer.CompositionConstants.REQUIRE_OR_ORIGINAL;
import static composer.CompositionConstants.SEMICOLON;
import static composer.CompositionConstants.TAB;
import static composer.CompositionConstants.TRUE;
import static composer.CompositionConstants.WS;
import static composer.CompositionConstants._;

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import composer.CompositionException;
import composer.FSTGenComposerExtension;
import composer.rules.ContractComposition;
import composer.rules.meta.FeatureModelInfo;
import composer.rules.meta.JavaMethodMeta;

import de.ovgu.cide.fstgen.ast.FSTNode;
import de.ovgu.cide.fstgen.ast.FSTNonTerminal;
import de.ovgu.cide.fstgen.ast.FSTTerminal;

/**
 * Contract composition for metaproduct desgined to use contracts instead of method inlining during theorem proving
 * 
 * @author Stefan Krueger
 * @author Sebastian Krieter
 * 
 */
public class ContractCompositionMetaUseContracts extends ContractComposition {

	private FeatureModelInfo modelInfo;
	private static final String delimiter = SEMICOLON + NEWLINE;

	private static final String domMarker = " ## ";
	private static final String domDispContractmarker = " ### ";
	private static final String assMarker = "#####";
	private static final String FeatureModelMarker = "%FM.%";
	
	private static final Pattern keywordPattern = Pattern.compile("(^|;)[^(requires|ensures|assignable)]*");
	private static final Pattern featurePattern = Pattern.compile("([(]|[\\s])*FM[.]FeatureModel[.]");

	public ContractCompositionMetaUseContracts(final String contract_style) {
		super(contract_style);
	}

	public ContractCompositionMetaUseContracts(final String contract_style, final FeatureModelInfo model) {
		super(contract_style);
		modelInfo = model;
	}

	/**
	 * Calculates the name of the feature-state for a given {@link FSTNode} below the feature-node (without "FeatureModel.")
	 * 
	 * @param node the {@link FSTNOde}
	 * @return name of the selection-state of the feature
	 */
	private static String getFeatureState(final FSTNode node) {
		return JavaMethodMeta.getFeatureName(node).toLowerCase() + (FSTGenComposerExtension.key ? "" : "()");
	}
	
	@Override
	public void preCompose(final FSTTerminal terminal) {
		terminal.setBody(NOT_COMPOSED + NEWLINE + TAB
			+ ((modelInfo.isCoreFeature(JavaMethodMeta.getFeatureName(terminal))) 
				? "" 
				: REQUIRES + WS + FM_MODEL + getFeatureState(terminal) + OR_WS + REQUIRE_OR_ORIGINAL + SEMICOLON + NEWLINE + TAB) 
			+ terminal.getBody());
	}

	@Override
	public void compose(final FSTTerminal terminalA, final FSTTerminal terminalB, final FSTTerminal terminalComp, final FSTNonTerminal nonterminalParent)
			throws CompositionException {
		markAsComposed(terminalA);
		
		// Do not compose if contract empty
		if (equalsFeatureReq(terminalA) && equalsFeatureReq(terminalB)) {
			terminalComp.setBody("");
			return;
		}

		String oldDisp = null, oldDom = null;
		final FSTTerminal methodB = (FSTTerminal) terminalB.getParent().getParent().getParent().getChildren().get(FST_METHOD_INDEX);
		final String methodName = getMethodName(methodB);
		final String returnType = JavaMethodMeta.getReturnType(methodB.getBody(), methodName);
		final String bFeatureName = terminalB.getOriginalFeatureName();
		String previousRefinementName = methodName + _ + bFeatureName;
		
		// Usually, terminalB == last Composition result. During first composition, terminalB == contract of introductory feature.  
		final boolean first = !terminalHasDomainMethod(terminalB);
		if (first) {
			//If first composition, no previous dispatcher method => terminalB used as dispatcher contract and domain contract.
			markAsComposed(terminalB);
			oldDisp = terminalB.getBody();
			oldDom = oldDisp;
		} else {
			// Check whether there is already a dispatcher method with the "same" name. If so, update variable holding name ofprevious refinement.
			final List<FSTNode> terminalBClassElements = terminalB.getParent().getParent().getParent().getParent().getChildren();
			for (final FSTNode child : terminalBClassElements) {
				if (child.getName().contains(DISPATCH)
						&& returnType.equals(JavaMethodMeta.getReturnType(((FSTTerminal) ((FSTNonTerminal) child).getChildren().get(FST_METHOD_INDEX)).getBody(), methodName + _
								+ bFeatureName))) {
					previousRefinementName = DISPATCH_ + previousRefinementName;
					break;
				}
			}

			// Decomposition of body according to marker. For composition, see end of method.
			final String[] bodies = terminalB.getBody().split(domDispContractmarker);
			if (bodies.length == 2) {
				oldDom = bodies[0];
				oldDisp = bodies[1];
				final int lDMInd = oldDom.lastIndexOf(domMarker);
				if (lDMInd >= 0) {
					oldDom = oldDom.substring(lDMInd + domMarker.length());
				}
			} else {
				oldDisp = bodies[0];
				oldDom = "";
			}
		}
		
		// Collect requires and ensures clauses from previous domain method for new doman and dispatcher method.
		// These clauses are only used when contract (terminalA) contains keyword \original.
		String domBody = terminalA.getBody();
		StringBuilder ensuresDom = null, requiresDom = null;
		final String bFeatureNameLow = bFeatureName.toLowerCase();
		final String impliesBFM = FM_MODEL + bFeatureNameLow + IMPLICATION_WS;
		if (oldDom != null && domBody.contains(ORIGINAL_KEYWORD)) {
			final Matcher m = keywordPattern.matcher(oldDom);
			if (m.find()) {
				requiresDom = new StringBuilder();
				ensuresDom = new StringBuilder();
				int start = m.end();
				while (m.find()) {
					final int end = m.start();
					final String line = oldDom.substring(start, end);
					final boolean featurePatternFound = featurePattern.matcher(line).find();
					if (line.startsWith(REQUIRES) && !line.toLowerCase().contains((FM_MODEL + bFeatureName).toLowerCase())) {
						appendClause(requiresDom, impliesBFM, line.substring(REQUIRES.length()), featurePatternFound);
					} else if (line.startsWith(ENSURES)) {
						appendClause(ensuresDom, impliesBFM, line.substring(ENSURES.length()), featurePatternFound);
					}
					start = m.end();
				}
			}
		}
		
		// Collect requires, ensures, and assignable clauses from previous dispatcher method for new dispatcher method.
		Matcher m = keywordPattern.matcher(oldDisp);
		Set<String> locSet = new HashSet<>();
		final StringBuilder ensuresDisp = new StringBuilder(), requiresDisp = new StringBuilder();
		String featureReq = FM_MODEL + bFeatureNameLow + OR_WS + REQUIRE_OR_ORIGINAL;
		if (m.find()) {
			int start = m.end();
			while (m.find()) {
				final int end = m.start();
				final String line = oldDisp.substring(start, end);
				final boolean featurePatternFound = featurePattern.matcher(line).find();
				if (line.startsWith(REQUIRES)) {
					final String clauseWithoutReq = line.substring(REQUIRES.length());
					if (line.contains(REQUIRE_OR_ORIGINAL)) {
						featureReq = clauseWithoutReq;
					} else {
						appendClause(requiresDisp, impliesBFM, clauseWithoutReq, featurePatternFound);
					}
				} else if (line.startsWith(ENSURES)) {
					appendClause(ensuresDisp, impliesBFM, line.substring(ENSURES.length()), featurePatternFound);
				} else if (line.startsWith(ASSIGNABLE)) {
					Collections.addAll(locSet, line.substring(ASSIGNABLE.length()).split(REGEX_COMMA_WS));
				}
				start = m.end();
			}
		}

		// Build requires, ensures, and assignable clauses for new domain and dispatcher methods.
		Set<String> dispLocSet = new HashSet<>();
		final StringBuilder contractBody = new StringBuilder();
		final StringBuilder dispContractBody = new StringBuilder();
		final String impliesFM = FM_MODEL + terminalA.getOriginalFeatureName().toLowerCase() + IMPLICATION_WS;
		
		m = keywordPattern.matcher(domBody);
		if (m.find()) {
			int start = m.end();

			// Adds clauses to dispatcher method contract for when feature of terminalB is not selected.
			if (requiresDisp.length() != 0) {
				dispContractBody.append(REQUIRES);
				dispContractBody.append(WS);
				dispContractBody.append(LBRACE);
				dispContractBody.append("!");
				dispContractBody.append(impliesFM);
				dispContractBody.append(requiresDisp);
				dispContractBody.append(RBRACE);
				dispContractBody.append(delimiter);
			}

			while (m.find()) {
				
				final String dispatchKeywordIfFirst = first ? "" : DISPATCH_;
				final int end = m.start();
				final String line = domBody.substring(start, end);
				final boolean origA = line.contains(ORIGINAL_KEYWORD);
				final boolean origCallA = line.contains(ORIGINAL_CALL);
				
				if (line.startsWith(REQUIRES)) {
					final String origDomRep = origA ? line.replace(ORIGINAL_KEYWORD, (requiresDom != null && requiresDom.length() > 0) ? LBRACE + requiresDom.toString() + RBRACE : TRUE) : line;
					contractBody.append(origDomRep);
					contractBody.append(delimiter);
					
					final int reqOrInd = line.lastIndexOf(REQUIRE_OR_ORIGINAL);
					if (reqOrInd >= 0) {
						dispContractBody.append(line.substring(0, reqOrInd) + featureReq);
					} else {
						String origRep = origA ? line.replace(ORIGINAL_KEYWORD, (requiresDisp.length() > 0) ? LBRACE + requiresDisp.toString() + RBRACE : TRUE) : line;
						origRep = origCallA ? origRep.replace(ORIGINAL_CALL, dispatchKeywordIfFirst + previousRefinementName + LBRACE) : origRep;
						appendFullClause(dispContractBody, REQUIRES, impliesFM, origA, origRep);
					}
					
					dispContractBody.append(delimiter);
				} else if (line.startsWith(ENSURES)) {
					String origRep = origA ? line.replace(ORIGINAL_KEYWORD, (ensuresDisp.length() > 0) ? LBRACE + ensuresDisp.toString() + RBRACE : TRUE) : line;
					origRep = origCallA ? origRep.replace(ORIGINAL_CALL, dispatchKeywordIfFirst + previousRefinementName + LBRACE) : origRep;
					
					String origDomRep = origA ? line.replace(ORIGINAL_KEYWORD, (ensuresDom != null && ensuresDom.length() > 0) ? LBRACE + ensuresDom.toString() + RBRACE : TRUE) : line;
					origDomRep = origCallA ? origDomRep.replace(ORIGINAL_CALL, dispatchKeywordIfFirst + previousRefinementName + LBRACE) : origDomRep;
					
					contractBody.append(origDomRep);
					contractBody.append(delimiter);
					
					appendFullClause(dispContractBody, ENSURES, impliesFM, origA, origRep);
					dispContractBody.append(delimiter);
				} else if (line.startsWith(ASSIGNABLE)) {
					Collections.addAll(dispLocSet, line.substring(ASSIGNABLE.length()).split(REGEX_COMMA_WS));
					if (!locSet.contains(EVERYTHING)) {
						dispLocSet.removeAll(locSet);
						dispLocSet.remove(NOTHING);
						dispLocSet.remove(EVERYTHING);
						final Set<String> tmpLocSet = new HashSet<>();
						for (final String el : dispLocSet) {
							dispContractBody.append(ENSURES);
							dispContractBody.append(WS);
							dispContractBody.append(LBRACE);
							dispContractBody.append("!");
							dispContractBody.append(impliesFM);
							dispContractBody.append(LBRACE);
							dispContractBody.append("\\old(");
							dispContractBody.append(el);
							dispContractBody.append(") == ");
							dispContractBody.append(el);
							dispContractBody.append(RBRACE);
							dispContractBody.append(RBRACE);
							dispContractBody.append(delimiter);

							tmpLocSet.add(assMarker + el);
						}
						dispLocSet = tmpLocSet;
					}
				}
				start = m.end();
			}
		}

		final boolean hasDisp = ensuresDisp.length() != 0;
		final boolean retIsNotVoid = !returnType.isEmpty();

		if (hasDisp || retIsNotVoid) {
			dispContractBody.append(ENSURES);
			dispContractBody.append(WS);
			dispContractBody.append(LBRACE);
			dispContractBody.append("!");
			dispContractBody.append(impliesFM);
			dispContractBody.append(ensuresDisp);
			dispContractBody.append(RBRACE);
			dispContractBody.append(delimiter);
		}

		final HashSet<String> tmpLocSet = new HashSet<>();
		for (final String el : locSet) {
			if (el.startsWith(assMarker)) {
				contractBody.append(ENSURES);
				contractBody.append(WS);
				contractBody.append(LBRACE);
				contractBody.append("!");
				contractBody.append(impliesBFM);
				contractBody.append(LBRACE);
				contractBody.append("\\old(");
				contractBody.append(el);
				contractBody.append(") == ");
				contractBody.append(el);
				contractBody.append(RBRACE);
				contractBody.append(RBRACE);
				contractBody.append(delimiter);
				tmpLocSet.add(el.substring(assMarker.length()));
			} else {
				tmpLocSet.add(el);
			}

		}
		locSet = tmpLocSet;
		locSet.addAll(dispLocSet);
		if (locSet.contains(EVERYTHING) || locSet.isEmpty()) {
			locSet.clear();
			locSet.add(EVERYTHING);
		} else if (locSet.size() != 1) {
			locSet.remove(NOTHING);
		}

		final StringBuilder assignable = new StringBuilder(ASSIGNABLE + WS);
		for (final String el : locSet) {
			if (!el.trim().isEmpty()) {
				assignable.append(el);
				assignable.append(COMMA);
			}
		}
		final String assignableC = assignable.toString().substring(0, assignable.length() - 1) + SEMICOLON;
		contractBody.append(assignableC);
		dispContractBody.append(assignableC);

		final String dispBody = dispContractBody.toString();

		domBody = contractBody.toString();
		if (first) {
			domBody = REQUIRES + WS + FM_MODEL + bFeatureNameLow + delimiter + oldDisp + domMarker + bFeatureName + domMarker
					+ domBody;
		}

		terminalComp.setBody(domBody + domDispContractmarker + dispBody);
	}

	private void appendFullClause(final StringBuilder dispContractBody, final String keyword, final String impliesFM, final boolean origA, String origRep) {
		final String keywordWS = keyword + WS;
		dispContractBody.append(keywordWS);
		dispContractBody.append(LBRACE);
		dispContractBody.append(origA ? "" : impliesFM);
		dispContractBody.append(origRep.substring(keywordWS.length()));
		dispContractBody.append(RBRACE);
	}

	private void appendClause(final StringBuilder clauseSB, final String impliesBFM, final String line, final boolean featurePatternFound) {
		if (clauseSB.length() > 0) {
			clauseSB.append(AND_WS);
		}
		clauseSB.append(LBRACE);
		clauseSB.append(featurePatternFound ? "" : impliesBFM);
		clauseSB.append(line);
		clauseSB.append(RBRACE);
	}

	private void markAsComposed(final FSTTerminal terminalB) {
		terminalB.setBody(terminalB.getBody().replace(NOT_COMPOSED + NEWLINE, ""));
	}

	private boolean equalsFeatureReq(final FSTTerminal terminal) {
		final String body = terminal.getBody();
		return body != null && (body.isEmpty() || body.trim().equals(REQUIRES + WS + FM_MODEL + terminal.getOriginalFeatureName().toLowerCase() + OR_WS + REQUIRE_OR_ORIGINAL + SEMICOLON));
	}

	@Override
	public void postCompose(final FSTTerminal terminal) {
		String body = terminal.getBody();

		if (removeRequireOrOriginal(body).trim().isEmpty()) {
			terminal.setBody("");
			return;
		}

		if (FSTGenComposerExtension.key && body.replace("@", "").trim().isEmpty()) {
			return;
		}

		final FSTTerminal fstTerminal = (FSTTerminal) terminal.getParent().getParent().getParent().getChildren().get(FST_METHOD_INDEX);
		final String fstTBody = fstTerminal.getBody();
		final String methodName = fstTerminal.getName().contains(LBRACE) ? getMethodName(fstTerminal) : fstTerminal.getName();
		final String params = JavaMethodMeta.getParameterNames(fstTerminal);
		final String returnType = JavaMethodMeta.getReturnType(fstTBody, methodName);

		final int ind = fstTBody.indexOf("{") + 1;

		final String resultEQOldEnsures = ENSURES + " \\\\result == \\\\old(" + methodName + LBRACE + params + RBRACE + RBRACE + SEMICOLON + NEWLINE + TAB + ENSURES + WS;
		final String FeatureModelPlaceHolder = TAB + REQUIRES + WS + FeatureModelMarker + SEMICOLON + NEWLINE;
		if (fstTBody.charAt(ind) == JavaMethodOverridingMetaUseContracts.domDispMethodMarker) {
			//dispatch
			final String[] bodies = terminal.getBody().split(domDispContractmarker);
			body = bodies.length == 2 ? bodies[1] : bodies[0];
			if (CONSTRUCTOR_CONCATENATION.equals(fstTerminal.getCompositionMechanism())) {
				body = FeatureModelPlaceHolder + body;
			} else if (!returnType.isEmpty() && methodName.startsWith(DISPATCH_)) {
				body = body.replaceFirst(ENSURES + WS, resultEQOldEnsures);
			}
			body = body.replace(assMarker, "");
			terminal.setBody(body);
			body = transformIntoAbstractContract(terminal, true);

		} else {
			if (body.contains(domDispContractmarker)) {
				//domain				
				final String[] bodies = terminal.getBody().split(domDispContractmarker);
				final String domain = bodies[0];
				final String[] domainCor = domain.split(domMarker);

				if (domainCor.length == 3) {
					if ((domainCor[1].equals(fstTerminal.getOriginalFeatureName()))) {
						body = domainCor[0];
					} else {
						body = domainCor[2];
					}
				} else {
					body = domainCor[0];
				}
				if (!returnType.isEmpty()) {
					body = body.replaceFirst(ENSURES + WS, resultEQOldEnsures);
				}
			} else {
				//Constructor
				final String reqFeatName = REQUIRES + WS + FM_MODEL + terminal.getOriginalFeatureName().toLowerCase();
				if (!body.contains(reqFeatName)) {
					body = reqFeatName + delimiter + body;
				}
			}
			if (CONSTRUCTOR_CONCATENATION.equals(fstTerminal.getCompositionMechanism())) {
				body = FeatureModelPlaceHolder + body;
			}
			body = body.replace(assMarker, "");
			terminal.setBody(body);
			body = transformIntoAbstractContract(terminal, false);
		}

		body = body.replace(" || " + REQUIRE_OR_ORIGINAL, "");
		body = body.replace(FINAL_CONTRACT, "");
		body = body.replace("requires  || ", "");
		body = body.replace(ORIGINAL_KEYWORD, "true");
		body = body.replace(NOT_COMPOSED, "");

		terminal.setBody(body);

		body = terminal.getBody();

		while (body.contains("\r\n\t\r\n\t") || body.contains("\r\n\t \r\n\t")) {
			body = body.replaceAll("\r\n[\\s]*\r\n\t", "\r\n\t");
		}

		body = body.replaceAll("\r\n\t([\\w])", "\r\n\t $1");
		body = body.replaceAll("\r\n\t([\\s]*)", "\r\n\t  @$1");
		if (!body.endsWith("\r\n\t ")) {
			body = body + "\r\n\t ";
		}
		body = TAB + "public normal_behaviour" + NEWLINE + body;

		terminal.setBody(body);
	}

	public void setFeatureModelInfo(final FeatureModelInfo model) {
		modelInfo = model;
	}

	private int aggregateClauses(final StringBuilder clause, final String[] contracts, int i, String line) {
		if (clause.length() > 0) {
			clause.append(AND_WS);
		}
		final String cleanedLine = line.substring(line.indexOf(WS) + 1);
		final boolean setBrackets = (!(cleanedLine.contains(FM_MODEL) || cleanedLine.contains(REQUIRE_OR_ORIGINAL)) && cleanedLine.contains(WS))
				|| (cleanedLine.contains(FM_MODEL) && (cleanedLine.indexOf(FM_MODEL) != cleanedLine.lastIndexOf(FM_MODEL)) && (cleanedLine.contains("==>") || cleanedLine
						.contains("||")));
		if (setBrackets) {
			clause.append(LBRACE);
		}

		clause.append(cleanedLine);
		while (!line.endsWith(SEMICOLON)) {
			line = contracts[++i].replace("@", "").trim();
			clause.append(line);
		}

		if (setBrackets) {
			clause.append(RBRACE);
		}
		return i;
	}

	private String getMethodName(final FSTTerminal methodB) {
		return methodB.getName().substring(0, methodB.getName().indexOf("("));
	}

	/**
	 * Removes clause with disjunction of selection states from specification body
	 * 
	 * @param body specification body
	 * @return specification body without disjunction of selection states
	 */
	private String removeRequireOrOriginal(final String body) {
		return body.replaceAll("requires FM.FeatureModel.[\\w]+" + (FSTGenComposerExtension.key ? "" : "\\(\\)") + " \\|\\| " + REQUIRE_OR_ORIGINAL + ";", "");
	}

	private boolean terminalHasDomainMethod(final FSTTerminal terminal) {
		final FSTNonTerminal grandGrandParent = terminal.getParent().getParent().getParent();
		final String methodName = getMethodName(((FSTTerminal) grandGrandParent.getChildren().get(FST_METHOD_INDEX))) + _;
		for (final FSTNode child : grandGrandParent.getParent().getChildren()) {
			if (child.getName().startsWith(methodName)) {
				return true;
			}
		}
		return false;
	}

	private String transformIntoAbstractContract(final FSTTerminal contract, final boolean dispatch) {
		final String contractBody = contract.getBody();
		final StringBuilder ensures = new StringBuilder(), requires = new StringBuilder(), assignable = new StringBuilder();
		final String[] contracts = contractBody.split("\\r?\\n");
		for (int i = 0; i < contracts.length; i++) {
			final String line = contracts[i].replace("@", "").trim();
			if (line.startsWith(REQUIRES)) {
				i = aggregateClauses(requires, contracts, i, line);
			} else if (line.startsWith(ENSURES)) {
				i = aggregateClauses(ensures, contracts, i, line);
			} else if (line.startsWith(ASSIGNABLE)) {
				assignable.append(line.substring(ASSIGNABLE.length()));
			}
		}

		final String methodName = contract.getParent().getParent().getParent().getName();
		final String placeholderName = !methodName.contains(LBRACE) ? methodName : ((dispatch) ? DISPATCH_ : "") + methodName.substring(0, methodName.indexOf(LBRACE)) + _
				+ contract.getOriginalFeatureName();
		final StringBuilder ret = new StringBuilder();
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
		ret.append((assignable.length() != 0) ? assignable.toString() + "\n" : EVERYTHING + SEMICOLON + NEWLINE);

		return ret.toString();
	}

}