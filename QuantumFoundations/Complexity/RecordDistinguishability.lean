import QuantumFoundations.Complexity.NormalizedBranches
import QuantumFoundations.Complexity.ProxyCertificates

/-!
# C5 — Distinguishability from an explicit record phase flip

The readout cost is not inferred from spatial locality.  Instead, a supplied
finite 2-local circuit is required to implement the exact phase reflection
`2 P_j - I`, and that concrete circuit is used as the upper-bound witness.
-/

namespace QuantumFoundations.Complexity

open scoped InnerProductSpace

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

/-- The exact phase reflection associated with record projector `P_j`:
`2 P_j - I`. -/
def recordPhaseFlip {n K : ℕ}
    (Λ : LabeledResolution n K) (j : Fin K) : H n →ₗ[ℂ] H n :=
  (2 : ℂ) • rproj Λ j - LinearMap.id

/-- A supplied site circuit exactly implements the record phase reflection
after transport to `H (d^N)`. -/
def ImplementsRecordPhaseFlip {N d K : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (C : Circuit N d)
    (Λ : LabeledResolution (d ^ N) K) (j : Fin K) : Prop :=
  Circuit.evalOnH C e = recordPhaseFlip Λ j

/-- The record phase flip fixes the normalized branch with its selected
label. -/
theorem recordPhaseFlip_apply_same {n K R : ℕ} [NeZero R]
    (recs : Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : IsRecordedOn ψ recs) (r : Fin R) (j : Fin K) :
    recordPhaseFlip (recs r) j (normalizedBranch recs ψ j) =
      normalizedBranch recs ψ j := by
  simp [recordPhaseFlip, recordProj_normalizedBranch_same recs ψ hrec r j]
  module

/-- The record phase flip negates every normalized branch carrying a
different label. -/
theorem recordPhaseFlip_apply_other {n K R : ℕ} [NeZero R]
    (recs : Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : IsRecordedOn ψ recs) (r : Fin R) (i j : Fin K) (hij : i ≠ j) :
    recordPhaseFlip (recs r) j (normalizedBranch recs ψ i) =
      -normalizedBranch recs ψ i := by
  simp [recordPhaseFlip,
    recordProj_normalizedBranch_other recs ψ hrec r i j hij]

/-- The self-inner-product of a normalized nonzero branch is one. -/
theorem normalizedBranch_inner_self {n K R : ℕ} [NeZero R]
    (recs : Fin R → LabeledResolution n K) (ψ : H n) (i : Fin K)
    (hi : branch recs ψ i ≠ 0) :
    ⟪normalizedBranch recs ψ i, normalizedBranch recs ψ i⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, normalizedBranch_norm recs ψ i hi]
  norm_num

/-- An explicit circuit implementing a record phase flip distinguishes two
distinct nonzero normalized recorded branches at every threshold
`0 ≤ δ ≤ 1`. -/
theorem record_phase_flip_distinguishesAt
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (recs : Fin R → LabeledResolution (d ^ N) K) (ψ : H (d ^ N))
    (hrec : IsRecordedOn ψ recs) (r₀ : Fin R) (i j : Fin K)
    (hij : i ≠ j) (hi : branch recs ψ i ≠ 0) (hj : branch recs ψ j ≠ 0)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (D : Circuit N d)
    (hD : ImplementsRecordPhaseFlip e D (recs r₀) j) :
    DistinguishesAt e
      (normalizedBranch recs ψ i) (normalizedBranch recs ψ j) δ D := by
  have hDa : Circuit.evalOnH D e (normalizedBranch recs ψ i) =
      -normalizedBranch recs ψ i := by
    rw [hD]
    exact recordPhaseFlip_apply_other recs ψ hrec r₀ i j hij
  have hDb : Circuit.evalOnH D e (normalizedBranch recs ψ j) =
      normalizedBranch recs ψ j := by
    rw [hD]
    exact recordPhaseFlip_apply_same recs ψ hrec r₀ j
  have hia := normalizedBranch_inner_self recs ψ i hi
  have hjb := normalizedBranch_inner_self recs ψ j hj
  unfold DistinguishesAt
  rw [hDa, hDb, inner_neg_right, hia, hjb]
  norm_num
  rcases hδ0.eq_or_lt with hzero | _
  · simpa [hzero]
  · exact hδ1

/-- A supplied exact record-readout circuit gives a distinguishability upper
bound equal to its own circuit length. -/
theorem record_phase_flip_gives_distinguishability_upper_bound
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (recs : Fin R → LabeledResolution (d ^ N) K) (ψ : H (d ^ N))
    (hrec : IsRecordedOn ψ recs) (r₀ : Fin R) (i j : Fin K)
    (hij : i ≠ j) (hi : branch recs ψ i ≠ 0) (hj : branch recs ψ j ≠ 0)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (D : Circuit N d)
    (hD : ImplementsRecordPhaseFlip e D (recs r₀) j) :
    HasDistinguishabilityUpperBound e
      (normalizedBranch recs ψ i) (normalizedBranch recs ψ j) δ
      (Circuit.length D) := by
  exact ⟨D, le_rfl, record_phase_flip_distinguishesAt
    e recs ψ hrec r₀ i j hij hi hj δ hδ0 hδ1 D hD⟩

#print axioms record_phase_flip_gives_distinguishability_upper_bound

end

end QuantumFoundations.Complexity
