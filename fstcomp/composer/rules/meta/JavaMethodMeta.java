package composer.rules.meta;

import composer.FSTGenComposerExtension;
import composer.rules.JavaMethodOverriding;
import de.ovgu.cide.fstgen.ast.FSTNode;
import de.ovgu.cide.fstgen.ast.FSTTerminal;

/**
 * 
 * @author Jens Meinicke
 * @author Stefan Krueger
 *
 */
public class JavaMethodMeta extends JavaMethodOverriding {

	
	public static String getFeatureName(FSTNode node) {
		if (node.getType().equals("Feature"))
			return node.getName().toLowerCase();
		else
			return getFeatureName(node.getParent());
	}
	
	
	protected String getParameterNames(FSTTerminal terminalA) {
		String parameter = terminalA.getBody().substring(
				terminalA.getBody().indexOf('(') + 1, terminalA.getBody().indexOf(')')).trim();
		String parameterNames = "";
		String[] p = parameter.split("[,]");
		for (int i = 0; i < p.length; i++) {
			String[] split = p[i].trim().split("[ ]");
			if (split.length < 2) {
				continue;
			}
			parameterNames += split[split.length-1];
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
		body =  body.substring(0, body.indexOf(name + "("));
		body = body.split("[ ]")[body.split("[ ]").length -1];
		body = body.replaceAll(" ", "");
		if (body.equals("void")) {
			return "";
		}
		return body;
	}
	
	protected String getLowFeatureName(FSTNode node) {
		return getFeatureName(node).toLowerCase() + (FSTGenComposerExtension.key ? "" : "()");
	}
}
