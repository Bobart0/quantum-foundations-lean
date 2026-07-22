import QuantumFoundations.Complexity.Models.Repetition.Readout

/-!
# C9d — Exact distinguishability complexity

The empty circuit cannot distinguish two unit vectors at threshold one,
whereas `recordReadoutCircuit` does so with one gate.  The proof uses the
generic `WithTop ℕ` infimum API and does not assume that arbitrary minima are
attained.
-/

namespace QuantumFoundations.Complexity

open scoped InnerProductSpace

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

namespace Circuit

/-- A circuit has length zero precisely when its gate list is empty. -/
theorem eq_nil_of_length_eq_zero {C : Circuit N d} (hC : C.length = 0) :
    C = [] := by
  exact List.eq_nil_of_length_eq_zero hC

/-- A zero-length circuit acts as the identity after transport to `H`. -/
theorem evalOnH_eq_id_of_length_eq_zero
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) {C : Circuit N d} (hC : C.length = 0) :
    C.evalOnH e = LinearMap.id := by
  rw [eq_nil_of_length_eq_zero hC]
  ext x
  simp [evalOnH]

end Circuit

/-- No zero-length circuit distinguishes two unit vectors at threshold one. -/
theorem not_distinguishesAt_one_of_length_zero
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N))
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (C : Circuit N d)
    (hC : C.length = 0) :
    ¬ DistinguishesAt e a b 1 C := by
  intro hdist
  unfold DistinguishesAt at hdist
  rw [Circuit.evalOnH_eq_id_of_length_eq_zero e hC] at hdist
  simp only [LinearMap.id_apply] at hdist
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ha, hb] at hdist
  norm_num at hdist

namespace RepetitionModel

/-- Every threshold-one distinguishing circuit for the two repetition
branches contains at least one gate. -/
theorem repetition_distinguishability_lower (R : ℕ) [NeZero R] :
    (1 : WithTop ℕ) ≤ distinguishabilityComplexity
      (sitesEquivR R) (zeroBranch R) (oneBranch R) 1 := by
  unfold distinguishabilityComplexity
  apply le_minCircuitLength_of_forall
  intro C hC
  by_cases hzero : C.length = 0
  · exact False.elim ((not_distinguishesAt_one_of_length_zero
      (sitesEquivR R) (zeroBranch R) (oneBranch R)
      (zeroBranch_norm R) (oneBranch_norm R) C hzero) hC)
  · exact Nat.one_le_iff_ne_zero.mpr hzero

/-- The exact distinguishability complexity of the explicit repetition
branches is one gate. -/
theorem repetition_distinguishabilityComplexity (R : ℕ) [NeZero R] :
    distinguishabilityComplexity
      (sitesEquivR R) (zeroBranch R) (oneBranch R) 1 = (1 : WithTop ℕ) :=
  le_antisymm (repetition_distinguishability_upper R)
    (repetition_distinguishability_lower R)

#print axioms repetition_distinguishabilityComplexity

end RepetitionModel

end


end QuantumFoundations.Complexity
