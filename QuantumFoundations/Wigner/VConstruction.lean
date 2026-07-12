import QuantumFoundations.Wigner.Defs

/-!
# W3 — Construction de `V` et propriétés de base (Bargmann §3, eqs 11-12a)

Préférer systématiquement les formes multiplicatives croisées dans les hypothèses
des lemmes (`γ • V z = T w − γ • e'` plutôt que des `⁻¹` dans les buts) — même
discipline que `sqrtOp`/`dilProj` côté Naimark pour éviter la casse `WithLp`/`⁻¹`.
-/

namespace QuantumFoundations.Wigner

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ} {T : H n → H n}

theorem inner_eImg_V (hT : IsWignerMap T) (z : H n) (hz : InPerp z) :
    ⟪eImg T, V T z⟫_ℂ = 0 := by
  sorry

theorem norm_V (hT : IsWignerMap T) (z : H n) (hz : InPerp z) :
    ‖V T z‖ = ‖z‖ := by
  sorry

/-- Colinéarité définitionnelle : `V z` est un multiple scalaire de phase de
`T` appliqué au représentant unitaire de `z` (Bargmann §3.2 : « Clearly,
`Vz = f'β' ∈ (Tf)‖z‖ = Tz` »). Rend la compatibilité `⟪e,x⟫ = 0` de W5 GRATUITE,
sans Cauchy-Schwarz. -/
theorem V_colinear (hT : IsWignerMap T) (z : H n) (hz : InPerp z) (hz0 : z ≠ 0) :
    ∃ δ : ℂ, ‖δ‖ = 1 ∧ V T z = δ • T (‖z‖⁻¹ • z) := by
  sorry

/-- (11) Module du produit scalaire préservé par `V` sur `𝒫`. -/
theorem norm_inner_V (hT : IsWignerMap T) (w x : H n) (hw : InPerp w) (hx : InPerp x) :
    ‖⟪V T w, V T x⟫_ℂ‖ = ‖⟪w, x⟫_ℂ‖ := by
  sorry

/-- (12) Partie réelle du produit scalaire préservée par `V` sur `𝒫`. -/
theorem re_inner_V (hT : IsWignerMap T) (w x : H n) (hw : InPerp w) (hx : InPerp x) :
    (⟪V T w, V T x⟫_ℂ).re = (⟪w, x⟫_ℂ).re := by
  sorry

/-- (12a) Si `⟪w,x⟫` est déjà réel, `V` le préserve exactement (pas seulement sa
partie réelle ou son module). -/
theorem inner_V_eq_of_im_eq_zero (hT : IsWignerMap T) (w x : H n) (hw : InPerp w)
    (hx : InPerp x) (hreal : (⟪w, x⟫_ℂ).im = 0) : ⟪V T w, V T x⟫_ℂ = ⟪w, x⟫_ℂ := by
  sorry

end
end QuantumFoundations.Wigner
