import QuantumFoundations.Complexity.ApproxRecordInterference
import QuantumFoundations.Complexity.Counting
import QuantumFoundations.Complexity.MinComplexity

/-!
# C8c — Thresholded interference lower bounds from approximate records

Above the strict error threshold `ηi + ηj < 2 * δ`, an interfering circuit
cannot leave any record region untouched.  The remaining cardinality argument
is exactly the Hilbert-space-independent C2 counting theorem.
-/

namespace QuantumFoundations.Complexity

open scoped InnerProductSpace

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

/-- Approximate redundant records force every threshold-interfering 2-local
circuit to satisfy the original finite counting bound. -/
theorem regions_card_le_two_mul_length_of_approx_interference
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (C : Circuit N d)
    (regions : Fin R → Finset (Fin N))
    (recs : Fin R → LabeledResolution (d ^ N) K)
    (a b : H (d ^ N)) (i j : Fin K) (ηi ηj δ : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (happrox : ApproxRecordedPairOn recs a b i j ηi ηj)
    (hlocal_i : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) i) (regions r))
    (hlocal_j : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) j) (regions r))
    (hpairwise : ∀ r r', r ≠ r' → Disjoint (regions r) (regions r'))
    (hthreshold : ηi + ηj < 2 * δ)
    (hinterferes : InterferesAt e a b δ C) :
    R ≤ 2 * Circuit.length C := by
  have htouched : ∀ r, ¬ Disjoint (Circuit.support C) (regions r) := by
    intro r hdisj
    have hupper := interference_expression_le_of_untouched_approx_records
      e C regions recs a b i j ηi ηj ha hb happrox hlocal_i hlocal_j r hdisj
    unfold InterferesAt at hinterferes
    linarith
  have hregions : Fintype.card (Fin R) ≤ (Circuit.support C).card :=
    regions_card_le_support_card regions (Circuit.support C) hpairwise htouched
  rw [Fintype.card_fin] at hregions
  exact hregions.trans (Circuit.circuit_support_card_le C)

/-- The per-circuit bound packages as an interference lower certificate of
`ceilHalf R`. -/
theorem approximate_records_give_interference_lower_bound
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (regions : Fin R → Finset (Fin N))
    (recs : Fin R → LabeledResolution (d ^ N) K)
    (a b : H (d ^ N)) (i j : Fin K) (ηi ηj δ : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (happrox : ApproxRecordedPairOn recs a b i j ηi ηj)
    (hlocal_i : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) i) (regions r))
    (hlocal_j : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) j) (regions r))
    (hpairwise : ∀ r r', r ≠ r' → Disjoint (regions r) (regions r'))
    (hthreshold : ηi + ηj < 2 * δ) :
    HasInterferenceLowerBound e a b δ (ceilHalf R) := by
  intro C hC
  apply ceilHalf_le_of_le_two_mul
  exact regions_card_le_two_mul_length_of_approx_interference
    e C regions recs a b i j ηi ηj δ ha hb happrox hlocal_i hlocal_j
    hpairwise hthreshold hC

/-- Approximate records lower-bound the actual `WithTop ℕ` interference
complexity above the strict error threshold. -/
theorem approximate_records_interferenceComplexity_lower_bound
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (regions : Fin R → Finset (Fin N))
    (recs : Fin R → LabeledResolution (d ^ N) K)
    (a b : H (d ^ N)) (i j : Fin K) (ηi ηj δ : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (happrox : ApproxRecordedPairOn recs a b i j ηi ηj)
    (hlocal_i : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) i) (regions r))
    (hlocal_j : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) j) (regions r))
    (hpairwise : ∀ r r', r ≠ r' → Disjoint (regions r) (regions r'))
    (hthreshold : ηi + ηj < 2 * δ) :
    (ceilHalf R : WithTop ℕ) ≤ interferenceComplexity e a b δ := by
  apply interferenceLowerBound_le_complexity
  exact approximate_records_give_interference_lower_bound
    e regions recs a b i j ηi ηj δ ha hb happrox hlocal_i hlocal_j
    hpairwise hthreshold

/-- Uniform error control `ηi,ηj ≤ η < δ` implies the primary strict
two-label threshold and hence the same interference lower bound. -/
theorem approximate_records_give_interference_lower_bound_uniform
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (regions : Fin R → Finset (Fin N))
    (recs : Fin R → LabeledResolution (d ^ N) K)
    (a b : H (d ^ N)) (i j : Fin K) (ηi ηj η δ : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (happrox : ApproxRecordedPairOn recs a b i j ηi ηj)
    (hlocal_i : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) i) (regions r))
    (hlocal_j : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) j) (regions r))
    (hpairwise : ∀ r r', r ≠ r' → Disjoint (regions r) (regions r'))
    (hηi : ηi ≤ η) (hηj : ηj ≤ η) (hηδ : η < δ) :
    HasInterferenceLowerBound e a b δ (ceilHalf R) := by
  apply approximate_records_give_interference_lower_bound
    e regions recs a b i j ηi ηj δ ha hb happrox hlocal_i hlocal_j hpairwise
  linarith

#print axioms regions_card_le_two_mul_length_of_approx_interference
#print axioms approximate_records_give_interference_lower_bound

end


end QuantumFoundations.Complexity
