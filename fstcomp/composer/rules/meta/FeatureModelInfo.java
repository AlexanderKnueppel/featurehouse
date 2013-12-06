package composer.rules.meta;

import java.util.List;


public interface FeatureModelInfo {

	/*
	 * erh�lt zwei Listen mit Feature-Namen:
	 * erste Liste enth�lt selektierte Features
	 * zweite Liste enth�lt Features, die definitiv nicht selektiert sind
	 * dritte Liste enth�lt Features, f�r die die Auswahl irrelevant ist
	 * 
	 * Ergebnis: true, wenn es eine g�ltige Kombination der Fehlenden Features gibt, sodass ein 
	 * 					valides Produkt entsteht
	 * 			 false, sonst
	 */
	public boolean possibleValid(List<String> selectedFeatures, List<String> unselectedFeatures, List<String> irrelevantFeatures);
	
	/*
	 * erh�lt zwei Feature-Namen
	 * liefert true, wenn kein Produkt beide Features enthalten kann, sonst false
	 */
	public boolean isComplementFeature(String firstFeature, String secondFeature);
	
	/*
	 * erh�lt List mit Features
	 * liefert true, wenn Liste ein AtomicSet ist (Features immer zusammen vorhanden sein m�ssen)
	 */
	public boolean isAtomicSet(List<String> featureList);
	
}
