import QuantumFoundations.EverettianAPI

/-!
Aggregate smoke contract for the public Everettian-facing facades.

The four detailed leaf audit files are compiled individually by CI. This
aggregate file checks that their public surfaces coexist under a single
`QuantumFoundations.EverettianAPI` import. It deliberately does not import the
leaf audit modules, because direct `lake env lean` invocations do not install
their `.olean` files as Lake library artifacts.
-/
namespace QuantumFoundations.Audit.EverettianDownstreamContracts

#check QuantumFoundations.ProbabilityAPI.Perspective
#check QuantumFoundations.FiniteTensorAPI.SuppliedBipartiteFactorization
#check QuantumFoundations.SelectorBridgeAPI.tSelectors_tensorMultiplicative_iff
#check QuantumFoundations.NaimarkImplementationAPI.implementationIndependent_of_residualNeutral

end QuantumFoundations.Audit.EverettianDownstreamContracts