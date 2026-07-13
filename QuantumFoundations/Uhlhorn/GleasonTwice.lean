import QuantumFoundations.Uhlhorn.GleasonExtend
import QuantumFoundations.Uhlhorn.Spectral

/-!
# U3b — L'argument « Gleason appliqué deux fois »

Combine `Gleason.gleason` (importé comme boîte noire), U3a
(`exists_projMeasure_of_frameFunctionOnLines`) et U2
(`eq_projL_of_positive_le_one_trace_one_inner_one`).
-/

namespace QuantumFoundations.Uhlhorn

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ}

/-- **U3b** : si `φ` envoie tout COSP (système orthonormé complet — en dimension
finie, toute base orthonormée) sur un COSP, alors `φ` préserve
`tr(φ(P)φ(Q)) = tr(PQ)` pour TOUTE paire `P, Q` — pas seulement les paires
orthogonales. -/
theorem traceProd_preserved_of_sendsONBToONB (hn : 3 ≤ n) (φ : Proj1 n → Proj1 n)
    (hφ : SendsONBToONB φ) :
    ∀ P Q : Proj1 n, TraceProd (φ P) (φ Q) = TraceProd P Q := by
  sorry

end
end QuantumFoundations.Uhlhorn
