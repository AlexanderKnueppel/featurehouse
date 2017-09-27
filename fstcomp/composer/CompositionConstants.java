package composer;

public class CompositionConstants {

	public static final int FST_METHOD_INDEX = 2;
	
	public static final String COMMA = ",";
	public static final String WS = " ";
	public static final String COMMA_SEP = COMMA + WS;
	public static final String COMPOSITION_CONJUNCTIVE = "FM.CompositionConjunctive";
	public static final String COMPOSITION_CONSECUTIVE = "FM.CompositionConsecutive";
	public static final String COMPOSITION_CUMULATIVE = "FM.CompositionCumulative";
	public static final String COMPOSITION_EXPLICIT = "FM.CompositionExplicit";
	public static final String COMPOSITION_PLAIN = "FM.CompositionPlain";
	public static final String REQUIRES = "requires";
	public static final String ENSURES = "ensures";
	public static final String ASSIGNABLE = "assignable";
	public static final String EVERYTHING = "\\everything";
	public static final String FEATURE = "Feature";
	public static final String FINAL_CONTRACT = "requires FM.Contract.finalContract;";
	public static final String FM_MODEL = "FM.FeatureModel.";
	public static final String LBRACE = "(";
	public static final String NOTHING = "\\nothing";
	public static final String RBRACE = ")";
	public static final String REGEX_WHITESPACE_PLUS = "\\s+";
	public static final String REGEX_WHITESPACE_STAR = "\\s*";
	public static final String REGEX_COMMA_WS = REGEX_WHITESPACE_STAR + COMMA + REGEX_WHITESPACE_STAR;
	public static final String REQUIRE_OR_ORIGINAL = "FM.Features.OrOriginal";
	public static final String SEMICOLON = ";";
	public static final String VOID = "void";
	public static final String NEWLINE = System.getProperty("line.separator", "\n");
	public static final String TAB = "\t";
	public static final String _ = "_";
	public static final String DISPATCH_ = "dispatch_";
	public static final String DISPATCH = "dispatch";
	public static final String PLAIN_CONTRACTING = "plain_contracting";
	public static final String CONSECUTIVE_CONTRACTING = "consecutive_contracting";
	public static final String EXPLICIT_CONTRACTING = "explicit_contracting";
	public static final String CONTRACT_OVERRIDING = "contract_overriding";
	public static final String CUMULATIVE_CONTRACTING = "cumulative_contracting";
	public static final String CONJUNCTIVE_CONTRACTING = "conjunctive_contracting";
	public static final String METHOD_BASED_COMPOSITION = "method_based";
	public static final String ORIGINAL_KEYWORD_CLAUSE = "\\original_clause";
	public static final String ORIGINAL_SPEC_KEYWORD = "\\original_spec";
	public static final String ORIGINAL_CASE_KEYWORD = "\\original_case";
	public static final String ORIGINAL_KEYWORD = "\\original";
	public static final String ORIGINAL_OR = "\\or_original";
	public static final String ORIGINAL_CALL = "original(";
	public static final String ORIGINAL_ASSIGNABLE = "original";
	public static final String RETURN = "return ";
	public static final String TRUE = WS + Boolean.TRUE.toString();
	public static final String NOT_COMPOSED = "\\not_composed";

	public static final String AND_WS = " && ";

	public static final String IMPLICATION_WS = " ==> ";

	public static final String CONSTRUCTOR_CONCATENATION = "ConstructorConcatenation";

	public static final String OR_WS = " || ";

}
