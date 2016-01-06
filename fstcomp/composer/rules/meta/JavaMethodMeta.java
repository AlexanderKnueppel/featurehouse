package composer.rules.meta;

import java.util.StringTokenizer;

import composer.CompositionConstants;
import composer.FSTGenComposerExtension;
import composer.rules.JavaMethodOverriding;

import de.ovgu.cide.fstgen.ast.FSTNode;
import de.ovgu.cide.fstgen.ast.FSTTerminal;

/**
 * Helper methods for metaproduct generation.
 * 
 * @author Jens Meinicke
 * @author Stefan Krueger
 * 
 */
public class JavaMethodMeta extends JavaMethodOverriding {

	/**
	 * Returns the name of the Feature for a {@link FSTNode} below the feature node
	 * 
	 * @param node the {@link FSTNode}
	 * @return name of the Feature
	 */
	public static String getFeatureName(final FSTNode node) {
		if (node.getType().equals(CompositionConstants.FEATURE)) {
			return node.getName().toLowerCase();
		} else {
			return getFeatureName(node.getParent());
		}
	}

	
	public static String getParameterNames(final FSTTerminal terminal) {
		final String body = terminal.getBody();
		final String parameters = body.substring(body.indexOf(CompositionConstants.LBRACE) + 1, body.indexOf(CompositionConstants.RBRACE)).trim();

		// No parameters
		if (parameters.isEmpty()) {
			return "";
		}

		final String[] parameterArray = parameters.split("\\s*,\\s*");
		final StringBuilder parameterNames = new StringBuilder();
		for (int i = 0; i < parameterArray.length; i++) {
			final String[] split = parameterArray[i].split(CompositionConstants.REGEX_WHITESPACE_PLUS);
			parameterNames.append(split[split.length - 1]);
			if (i < (parameterArray.length - 1)) {
				parameterNames.append(CompositionConstants.COMMA_SEP);
			}
		}
		return parameterNames.toString();
	}

	public static String getReturnType(String body, final String name) {
		// TODO: REVISE REGEXS \\w*\\W* AND \\W*\\(
		// remove @annotations and spaces between name and (
		body = body.replaceAll("@\\w*\\W*", "").replaceAll(name + "\\W*\\(", name + CompositionConstants.LBRACE);
		body = body.substring(0, body.indexOf(name + CompositionConstants.LBRACE));
		final String[] split = body.split(CompositionConstants.REGEX_WHITESPACE_PLUS);
		body = split[split.length - 1];
		if (body.equals(CompositionConstants.VOID)) {
			return "";
		}
		return body;
	}

	public static String getMethodName(final FSTTerminal terminal) {
		String methodName = terminal.getName();
		final StringTokenizer st = new StringTokenizer(methodName, CompositionConstants.LBRACE);
		if (st.hasMoreTokens()) {
			methodName = st.nextToken();
		}
		return methodName;
	}
	
	protected String getLowFeatureName(final FSTNode node) {
		return getFeatureName(node).toLowerCase() + (FSTGenComposerExtension.key ? "" : (CompositionConstants.LBRACE + CompositionConstants.RBRACE));
	}
}
