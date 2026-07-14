import QuantumFoundations.Uhlhorn.WignerProjectionForm
import QuantumFoundations.Uhlhorn.GleasonTwice

/-!
# U4/U5 — Assemblage final et Corollaire 1.2 de Šemrl

U4 combine U1 et U3b. U5 réduit `PreservesOrthogonality` (orthogonalité préservée
dans un seul sens, ni injectivité ni surjectivité supposées) à `SendsONBToONB` par
un argument de comptage de cardinalité valable en dimension finie, puis conclut via
U4 — c'est le théorème final.
-/

namespace QuantumFoundations.Uhlhorn

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ}

/-- **U4** (assemblage) : U1 + U3b — si `φ` envoie tout COSP sur un COSP, `φ` est
une symétrie de Wigner. -/
theorem wignerSymmetryProj_of_sendsONBToONB (hn : 3 ≤ n) (φ : Proj1 n → Proj1 n)
    (hφ : SendsONBToONB φ) : IsWignerSymmetryProj φ :=
  wigner_projection_form n φ (traceProd_preserved_of_sendsONBToONB hn φ hφ)

/-- **Sous-lemme A + B** : si `φ` préserve l'orthogonalité dans un seul sens,
l'image d'une base orthonormée `b` par des représentants unitaires choisis
(`exists_unit_vector_of_proj1`) est elle-même une famille orthonormée
(Sous-lemme A) ; en dimension finie, une famille orthonormée de cardinal `n`
forme automatiquement une base (Sous-lemme B,
`basisOfOrthonormalOfCardEqFinrank` + `Module.Basis.toOrthonormalBasis`, tous
deux préservant les valeurs POINTWISE — pas seulement à un reindexing près). -/
private theorem sendsONBToONB_of_preservesOrthogonality (hn : 3 ≤ n) (φ : Proj1 n → Proj1 n)
    (hφ : PreservesOrthogonality φ) : SendsONBToONB φ := by
  intro b
  have hex : ∀ i, ∃ x : H n, ‖x‖ = 1 ∧
      (φ (Proj1.mk_unit (b i) (b.norm_eq_one i)) : Submodule ℂ (H n)) = ℂ ∙ x :=
    fun i => exists_unit_vector_of_proj1 (φ (Proj1.mk_unit (b i) (b.norm_eq_one i)))
  choose x hx_unit hx_repr using hex
  -- Sous-lemme A : l'image `x` de `b` par `φ` (représentants unitaires) est orthonormée.
  have himages_orthonormal : Orthonormal ℂ x := by
    constructor
    · exact hx_unit
    · intro i j hij
      have hb_ortho : ⟪b i, b j⟫_ℂ = 0 := b.orthonormal.2 hij
      have hsub_ortho : (ℂ ∙ (b i)) ⟂ (ℂ ∙ (b j)) := by
        rw [Submodule.isOrtho_span]
        rintro a ha c hc
        simp only [Set.mem_singleton_iff] at ha hc
        rw [ha, hc]; exact hb_ortho
      have himg_ortho : (ℂ ∙ (x i)) ⟂ (ℂ ∙ (x j)) := by
        rw [← hx_repr i, ← hx_repr j]
        exact hφ (Proj1.mk_unit (b i) (b.norm_eq_one i)) (Proj1.mk_unit (b j) (b.norm_eq_one j))
          hsub_ortho
      exact Submodule.isOrtho_iff_inner_eq.mp himg_ortho (x i)
        (Submodule.mem_span_singleton_self (x i)) (x j) (Submodule.mem_span_singleton_self (x j))
  -- Sous-lemme B : `x`, orthonormée de cardinal `n = finrank (H n)`, complète en base.
  have hn0 : 0 < n := by omega
  haveI : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  have hcard : Fintype.card (Fin n) = Module.finrank ℂ (H n) := by simp
  set bas : Module.Basis (Fin n) ℂ (H n) := basisOfOrthonormalOfCardEqFinrank himages_orthonormal
    hcard with hbas
  have hbas_eq : (bas : Fin n → H n) = x :=
    coe_basisOfOrthonormalOfCardEqFinrank himages_orthonormal hcard
  have hxOrtho : Orthonormal ℂ bas := by rw [hbas_eq]; exact himages_orthonormal
  refine ⟨bas.toOrthonormalBasis hxOrtho, fun i => ?_⟩
  have heq := Module.Basis.coe_toOrthonormalBasis bas hxOrtho
  have hbi : (bas.toOrthonormalBasis hxOrtho) i = x i := by
    rw [show (bas.toOrthonormalBasis hxOrtho) i = (bas.toOrthonormalBasis hxOrtho : Fin n → H n) i
      from rfl, heq, hbas_eq]
  rw [hx_repr i, hbi]

/-- **U5 — Corollaire 1.2 de Šemrl** (Šemrl 2021, arXiv:2106.06182) : en dimension
finie `n ≥ 3`, toute application sur les projections de rang 1 qui préserve
l'orthogonalité DANS UN SEUL SENS est automatiquement une symétrie de Wigner. -/
theorem uhlhorn_finite_dim (hn : 3 ≤ n) (φ : Proj1 n → Proj1 n)
    (hφ : PreservesOrthogonality φ) : IsWignerSymmetryProj φ :=
  wignerSymmetryProj_of_sendsONBToONB hn φ (sendsONBToONB_of_preservesOrthogonality hn φ hφ)

end
end QuantumFoundations.Uhlhorn
