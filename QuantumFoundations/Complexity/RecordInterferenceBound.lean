import QuantumFoundations.Complexity.Main
import QuantumFoundations.Complexity.NormalizedBranches
import QuantumFoundations.Complexity.ProxyCertificates

/-!
# C4 — Interference lower bounds from redundant records

This file lifts the one-way nonzero-cross-amplitude result of C2 to the
two-cross-term Taylor–McCulloch interference proxy.  Since either orientation
may be nonzero, locality is required for both possible target labels.
-/

namespace QuantumFoundations.Complexity

open scoped InnerProductSpace

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

/-- For nonzero raw branches, normalization preserves whether a cross
amplitude through a linear operator is nonzero. -/
theorem normalized_cross_ne_zero_iff_raw_cross_ne_zero {n K R : ℕ} [NeZero R]
    (recs : Fin R → LabeledResolution n K) (ψ : H n) (i j : Fin K)
    (hi : branch recs ψ i ≠ 0) (hj : branch recs ψ j ≠ 0)
    (T : H n →ₗ[ℂ] H n) :
    ⟪normalizedBranch recs ψ i, T (normalizedBranch recs ψ j)⟫_ℂ ≠ 0 ↔
      ⟪branch recs ψ i, T (branch recs ψ j)⟫_ℂ ≠ 0 := by
  rw [normalizedBranch_eq_smul_branch, normalizedBranch_eq_smul_branch,
    map_smul, inner_smul_left, inner_smul_right]
  simp only [mul_ne_zero_iff]
  simp [norm_ne_zero_iff.mpr hi, norm_ne_zero_iff.mpr hj]

/-- Every exact 2-local circuit satisfying the two-cross-term interference
proxy between two distinct nonzero recorded branches has length at least
`ceilHalf R`.

Both `hlocal_i` and `hlocal_j` are essential: the proxy only guarantees that
one of its two oppositely oriented cross amplitudes is nonzero. -/
theorem interference_circuit_length_ge_of_redundant_records
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (regions : Fin R → Finset (Fin N))
    (recs : Fin R → LabeledResolution (d ^ N) K) (ψ : H (d ^ N))
    (hrec : IsRecordedOn ψ recs) (i j : Fin K) (hij : i ≠ j)
    (hi : branch recs ψ i ≠ 0) (hj : branch recs ψ j ≠ 0)
    (hlocal_i : ∀ r, IsLocalTo (transportedRecordProj e (recs r) i) (regions r))
    (hlocal_j : ∀ r, IsLocalTo (transportedRecordProj e (recs r) j) (regions r))
    (hpairwise : ∀ r r', r ≠ r' → Disjoint (regions r) (regions r'))
    (δ : ℝ) (hδ : 0 < δ) (C : Circuit N d)
    (hC : InterferesAt e
      (normalizedBranch recs ψ i) (normalizedBranch recs ψ j) δ C) :
    ceilHalf R ≤ Circuit.length C := by
  rcases one_cross_amplitude_ne_zero_of_interferesAt e
      (normalizedBranch recs ψ i) (normalizedBranch recs ψ j) δ C hδ hC with
    hijCross | hjiCross
  · have hraw :
        ⟪branch recs ψ i, Circuit.evalOnH C e (branch recs ψ j)⟫_ℂ ≠ 0 :=
      (normalized_cross_ne_zero_iff_raw_cross_ne_zero
        recs ψ i j hi hj (Circuit.evalOnH C e)).mp hijCross
    apply ceilHalf_le_of_le_two_mul
    exact regions_card_le_two_mul_circuit_length_of_cross_amplitude_ne_zero
      e C regions recs ψ hrec j i hij.symm hlocal_i hpairwise hraw
  · have hraw :
        ⟪branch recs ψ j, Circuit.evalOnH C e (branch recs ψ i)⟫_ℂ ≠ 0 :=
      (normalized_cross_ne_zero_iff_raw_cross_ne_zero
        recs ψ j i hj hi (Circuit.evalOnH C e)).mp hjiCross
    apply ceilHalf_le_of_le_two_mul
    exact regions_card_le_two_mul_circuit_length_of_cross_amplitude_ne_zero
      e C regions recs ψ hrec i j hij hlocal_j hpairwise hraw

/-- Exact redundant records certify the interference lower bound
`ceilHalf R` for the normalized branches. -/
theorem redundant_records_give_interference_lower_bound
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (regions : Fin R → Finset (Fin N))
    (recs : Fin R → LabeledResolution (d ^ N) K) (ψ : H (d ^ N))
    (hrec : IsRecordedOn ψ recs) (i j : Fin K) (hij : i ≠ j)
    (hi : branch recs ψ i ≠ 0) (hj : branch recs ψ j ≠ 0)
    (hlocal_i : ∀ r, IsLocalTo (transportedRecordProj e (recs r) i) (regions r))
    (hlocal_j : ∀ r, IsLocalTo (transportedRecordProj e (recs r) j) (regions r))
    (hpairwise : ∀ r r', r ≠ r' → Disjoint (regions r) (regions r'))
    (δ : ℝ) (hδ : 0 < δ) :
    HasInterferenceLowerBound e
      (normalizedBranch recs ψ i) (normalizedBranch recs ψ j) δ (ceilHalf R) := by
  intro C hC
  exact interference_circuit_length_ge_of_redundant_records
    e regions recs ψ hrec i j hij hi hj hlocal_i hlocal_j hpairwise δ hδ C hC

#print axioms redundant_records_give_interference_lower_bound

end

end QuantumFoundations.Complexity
