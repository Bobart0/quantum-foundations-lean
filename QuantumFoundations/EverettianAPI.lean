import QuantumFoundations.ProbabilityAPI
import QuantumFoundations.FiniteTensorAPI
import QuantumFoundations.SelectorBridgeAPI
import QuantumFoundations.NaimarkImplementationAPI

/-!
Façade additive destinée aux développements aval. Elle ne remplace pas
`ProbabilityAPI`, dont le contrat historique reste inchangé. Les sous-façades
conservent séparés :

* résultats conditionnels de probabilité ;
* calcul tensoriel fini ;
* ponts de sélecteurs ;
* invariance des implémentations de Naimark.

Les utilisateurs peuvent importer séparément `ProbabilityAPI`,
`FiniteTensorAPI`, `SelectorBridgeAPI` et `NaimarkImplementationAPI`, ou
importer cet ensemble avec `QuantumFoundations.EverettianAPI`.
-/
namespace QuantumFoundations.EverettianAPI
end QuantumFoundations.EverettianAPI
