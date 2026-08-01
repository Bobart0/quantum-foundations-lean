import QuantumFoundations.FiniteTensor.Operator
namespace QuantumFoundations.FiniteTensor
open QuantumFoundations
open Gleason
open scoped InnerProductSpace
noncomputable section
def partialTraceAncilla {n a : ℕ} (A : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a) : H n →ₗ[ℂ] H n := ∑ j : Fin a, ancillaBlockCoord (n := n) j ∘ₗ A ∘ₗ ancillaBlockSingle (n := n) j
theorem partialTraceAncilla_zero {n a : ℕ} : partialTraceAncilla (0 : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a) = 0 := by ext x; simp [partialTraceAncilla]
theorem partialTraceAncilla_add {n a : ℕ} (A B : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a) : partialTraceAncilla (A + B) = partialTraceAncilla A + partialTraceAncilla B := by simp only [partialTraceAncilla, LinearMap.add_comp, LinearMap.comp_add, Finset.sum_add_distrib]
theorem partialTraceAncilla_smul {n a : ℕ} (c : ℂ) (A : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a) : partialTraceAncilla (c • A) = c • partialTraceAncilla A := by simp only [partialTraceAncilla, LinearMap.smul_comp, LinearMap.comp_smul, Finset.smul_sum]
theorem partialTraceAncilla_id {n a : ℕ} : partialTraceAncilla (LinearMap.id : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a) = (a : ℂ) • (LinearMap.id : H n →ₗ[ℂ] H n) := by ext x; simp [partialTraceAncilla, LinearMap.sum_apply, ancillaBlockCoord_comp_single]
theorem trace_eq_sum_operatorEntry {d : ℕ} (A : H d →ₗ[ℂ] H d) : LinearMap.trace ℂ (H d) A = ∑ i : Fin d, operatorEntry A i i := by
  rw [LinearMap.trace_eq_sum_inner A (EuclideanSpace.basisFun (Fin d) ℂ)]
  rfl
theorem partialTraceAncilla_tensorOperator {n a : ℕ} (A : H n →ₗ[ℂ] H n) (B : H a →ₗ[ℂ] H a) : partialTraceAncilla (tensorOperator A B) = (LinearMap.trace ℂ (H a) B) • A := by
  have hterm (j : Fin a) : ancillaBlockCoord (n := n) j ∘ₗ tensorOperator A B ∘ₗ ancillaBlockSingle (n := n) j = operatorEntry B j j • A := by
    ext x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ancillaBlockCoord_tensorOperator]
    have hcoord : ∀ k : Fin a, ancillaBlockCoord (n := n) k (ancillaBlockSingle (n := n) j x) = if k = j then x else 0 := by
      intro k
      have h := LinearMap.congr_fun (ancillaBlockCoord_comp_single (n := n) k j) x
      by_cases hk : k = j
      · subst k
        simpa [if_pos rfl, LinearMap.comp_apply] using h
      · rw [if_neg hk] at h
        simpa [if_neg hk, LinearMap.comp_apply] using h
    simp_rw [hcoord]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b hb hbj
      simp [hbj]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [partialTraceAncilla]
  simp_rw [hterm]
  rw [← Finset.sum_smul]
  congr 1
  exact (trace_eq_sum_operatorEntry B).symm
end
end QuantumFoundations.FiniteTensor
