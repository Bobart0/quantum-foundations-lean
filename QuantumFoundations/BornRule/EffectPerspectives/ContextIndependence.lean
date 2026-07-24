import QuantumFoundations.BornRule.EffectPerspectives.Estimation

/-!
# QB5 — Context independence and derived effect additivity

Derives, from `EstimationRule.grain` alone (never assumed): context
independence of the weight of a given effect across every perspective in
which it occurs, zero-effect weight, unit-effect weight, and binary
additivity on effects. None of these appear as structure fields of
`EstimationRule`; all are theorems.
-/

namespace QuantumFoundations.BornRule.EffectPerspectives

noncomputable section

variable {n : ℕ}

/-! ## QB5.1 — Canonical effect weight -/

/-- The canonical weight an estimation rule assigns to a single effect: its
weight at outcome `0` of the binary perspective it generates. -/
def EstimationRule.effectWeight (E : EstimationRule n) (T : Effect n) : ℝ :=
  E.weight (binaryPerspective T) (0 : Fin 2)

/-! ## QB5.2 — Context-independence theorem -/

/-- **Context independence**, derived (not assumed): the weight assigned to
an outcome of any effect perspective equals the canonical weight of that
outcome's effect. -/
theorem contextual_weight_eq_effectWeight (E : EstimationRule n) (D : EffectPerspective n)
    (i : Fin D.outcomes) :
    E.weight D i = E.effectWeight (D.effects i) := by
  show E.weight D i = E.weight (binaryPerspective (D.effects i)) (0 : Fin 2)
  rw [E.grain (collapseToChosen D i) (0 : Fin 2)]
  trans (∑ k : Fin D.outcomes, if k = i then E.weight D k else 0)
  · rw [Finset.sum_ite_eq' Finset.univ i (fun k => E.weight D k)]
    simp
  · apply Finset.sum_congr rfl
    intro k _
    show (if k = i then E.weight D k else 0)
        = (if (if k = i then (0 : Fin 2) else 1) = 0 then E.weight D k else 0)
    by_cases hk : k = i <;> simp [hk]

/-! ## QB5.3 — Same effect in different contexts -/

theorem same_effect_same_weight (E : EstimationRule n)
    (D₁ : EffectPerspective n) (i₁ : Fin D₁.outcomes)
    (D₂ : EffectPerspective n) (i₂ : Fin D₂.outcomes)
    (h : (D₁.effects i₁ : Gleason.H n →ₗ[ℂ] Gleason.H n)
      = (D₂.effects i₂ : Gleason.H n →ₗ[ℂ] Gleason.H n)) :
    E.weight D₁ i₁ = E.weight D₂ i₂ := by
  rw [contextual_weight_eq_effectWeight E D₁ i₁, contextual_weight_eq_effectWeight E D₂ i₂,
    show D₁.effects i₁ = D₂.effects i₂ from Subtype.ext h]

/-! ## QB5.4 — Non-negativity -/

theorem effectWeight_nonneg (E : EstimationRule n) (T : Effect n) :
    0 ≤ E.effectWeight T :=
  E.nonneg (binaryPerspective T) (0 : Fin 2)

/-! ## QB5.5 — Derive zero-effect weight -/

theorem effectWeight_zero (E : EstimationRule n) : E.effectWeight (zeroEffect n) = 0 := by
  have hw0 : E.weight (duplicateZeroPerspective n) (0 : Fin 3) = E.effectWeight (zeroEffect n) := by
    rw [contextual_weight_eq_effectWeight E (duplicateZeroPerspective n) (0 : Fin 3),
      duplicateZeroPerspective_effect_zero]
  have hw1 : E.weight (duplicateZeroPerspective n) (1 : Fin 3) = E.effectWeight (zeroEffect n) := by
    rw [contextual_weight_eq_effectWeight E (duplicateZeroPerspective n) (1 : Fin 3),
      duplicateZeroPerspective_effect_one]
  have hgrain := E.grain (duplicateZeroRefinesBinary n) (0 : Fin 2)
  change E.effectWeight (zeroEffect n)
      = ∑ k : Fin 3, if (![(0 : Fin 2), 0, 1] k) = (0 : Fin 2)
          then E.weight (duplicateZeroPerspective n) k else 0 at hgrain
  rw [Fin.sum_univ_three] at hgrain
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at hgrain
  norm_num at hgrain
  rw [hw0, hw1] at hgrain
  linarith

/-! ## QB5.6 — Derive unit-effect weight -/

theorem effectWeight_one (E : EstimationRule n) : E.effectWeight (oneEffect n) = 1 := by
  have hnorm := E.normalized (binaryPerspective (oneEffect n))
  change (∑ k : Fin 2, E.weight (binaryPerspective (oneEffect n)) k) = 1 at hnorm
  rw [Fin.sum_univ_two] at hnorm
  have h0 : E.weight (binaryPerspective (oneEffect n)) (0 : Fin 2) = E.effectWeight (oneEffect n) := rfl
  have h1 : E.weight (binaryPerspective (oneEffect n)) (1 : Fin 2) = E.effectWeight (zeroEffect n) := by
    rw [contextual_weight_eq_effectWeight E (binaryPerspective (oneEffect n)) (1 : Fin 2),
      binaryPerspective_effect_one, complementEffect_one]
  rw [h0, h1, effectWeight_zero] at hnorm
  linarith

/-! ## QB5.7 — Derive binary additivity on effects -/

theorem effectWeight_add (E : EstimationRule n) (S T : Effect n)
    (hST : Gleason.IsEffect (S.1 + T.1)) :
    E.effectWeight (sumEffect S T hST) = E.effectWeight S + E.effectWeight T := by
  have hw0 : E.weight (splitPerspective S T hST) (0 : Fin 3) = E.effectWeight S := by
    rw [contextual_weight_eq_effectWeight E (splitPerspective S T hST) (0 : Fin 3),
      splitPerspective_effect_zero]
  have hw1 : E.weight (splitPerspective S T hST) (1 : Fin 3) = E.effectWeight T := by
    rw [contextual_weight_eq_effectWeight E (splitPerspective S T hST) (1 : Fin 3),
      splitPerspective_effect_one]
  have hgrain := E.grain (splitRefinesBinary S T hST) (0 : Fin 2)
  change E.effectWeight (sumEffect S T hST)
      = ∑ k : Fin 3, if (![(0 : Fin 2), 0, 1] k) = (0 : Fin 2)
          then E.weight (splitPerspective S T hST) k else 0 at hgrain
  rw [Fin.sum_univ_three] at hgrain
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at hgrain
  norm_num at hgrain
  rw [hw0, hw1] at hgrain
  linarith

end

end QuantumFoundations.BornRule.EffectPerspectives
