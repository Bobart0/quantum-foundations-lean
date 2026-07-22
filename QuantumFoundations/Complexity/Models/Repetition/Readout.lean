import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import QuantumFoundations.Complexity.Models.Repetition.Records
import QuantumFoundations.Complexity.RecordDistinguishability
import QuantumFoundations.Complexity.MinComplexity

/-!
# C9c — Constant-cost readout in the repetition model

The distinguished record site is site zero.  The gate is the orthogonal
reflection in the bit-one cell at that site: it has eigenvalue `-1` on bit
zero and `+1` on bit one.  Thus it is exactly the phase flip `2 P₁ - I`
required by the generic distinguishability API.
-/

namespace QuantumFoundations.Complexity.RepetitionModel

open scoped InnerProductSpace

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

/-- The canonical record site, available for every nonempty repetition model. -/
def firstSite (R : ℕ) [NeZero R] : Fin R := ⟨0, NeZero.pos R⟩

private theorem sitesCell_reflection_local (R : ℕ) (r : Fin R) (b : Fin 2) :
    IsLocalTo
      (sitesCell R r b).reflection.toLinearIsometry.toLinearMap {r} := by
  let rr : {x // x ∈ ({r} : Finset (Fin R))} := ⟨r, by simp⟩
  refine ⟨fun gl kl =>
    if gl = kl then (if kl rr = b then 1 else -1) else 0, ?_⟩
  intro g k
  change ⟪configurationBasis g,
    (sitesCell R r b).reflection (configurationBasis k)⟫_ℂ = _
  have hreflect :
      (sitesCell R r b).reflection (configurationBasis k) =
        if k r = b then configurationBasis k else -configurationBasis k := by
    rw [Submodule.reflection_apply, sitesCell_starProjection_configurationBasis]
    split_ifs <;> module
  rw [hreflect]
  by_cases hgk : g = k
  · subst g
    by_cases hk : k r = b
    · rw [if_pos hk]
      simp [configurationBasis, AgreesOff, rr, hk]
    · rw [if_neg hk]
      simp [configurationBasis, AgreesOff, rr, hk]
  · have hinner :
        ⟪configurationBasis g, configurationBasis k⟫_ℂ = 0 := by
      unfold configurationBasis
      rw [EuclideanSpace.inner_single_left]
      simp [hgk]
    by_cases hoff : AgreesOff {r} g k
    · have hrest :
          g ∘ (Subtype.val : {x // x ∈ ({r} : Finset (Fin R))} → Fin R) ≠
            k ∘ Subtype.val := by
        intro h
        apply hgk
        funext s
        by_cases hsr : s = r
        · subst s
          exact congrFun h rr
        · exact hoff s (by simpa using hsr)
      by_cases hk : k r = b
      · rw [if_pos hk, hinner]
        simp [hoff, hrest]
      · rw [if_neg hk, inner_neg_right, hinner]
        simp [hoff, hrest]
    · by_cases hk : k r = b
      · rw [if_pos hk, hinner]
        simp [hoff]
      · rw [if_neg hk, inner_neg_right, hinner]
        simp [hoff]

/-- The one-site reflection that reads the bit-one record at an arbitrary
site `r`.  Unlike `recordReadoutGate`, no `[NeZero R]` instance is needed: the
site `r` itself witnesses that `Fin R` is nonempty. -/
def recordReadoutGateAt (R : ℕ) (r : Fin R) : TwoLocalGate R 2 where
  unitary := (sitesCell R r 1).reflection
  support := {r}
  locality := sitesCell_reflection_local R r 1
  support_card_le_two := by simp

@[simp] theorem recordReadoutGateAt_support (R : ℕ) (r : Fin R) :
    (recordReadoutGateAt R r).support = {r} := rfl

@[simp] theorem recordReadoutGateAt_support_card (R : ℕ) (r : Fin R) :
    (recordReadoutGateAt R r).support.card = 1 := by simp

theorem recordReadoutGateAt_local (R : ℕ) (r : Fin R) :
    IsLocalTo
      (recordReadoutGateAt R r).unitary.toLinearIsometry.toLinearMap {r} :=
  (recordReadoutGateAt R r).locality

/-- The constant-cost readout circuit at an arbitrary site: a single
reflection gate. -/
def recordReadoutCircuitAt (R : ℕ) (r : Fin R) : Circuit R 2 :=
  [recordReadoutGateAt R r]

@[simp] theorem recordReadoutCircuitAt_length (R : ℕ) (r : Fin R) :
    (recordReadoutCircuitAt R r).length = 1 := rfl

/-- The singleton circuit at an arbitrary site implements the exact abstract
record phase flip. -/
theorem recordReadoutCircuitAt_implements (R : ℕ) (r : Fin R) :
    ImplementsRecordPhaseFlip
      (sitesEquivR R) (recordReadoutCircuitAt R r)
      (siteResolution R r) 1 := by
  unfold ImplementsRecordPhaseFlip
  apply LinearMap.ext
  intro x
  simp only [Circuit.evalOnH, recordReadoutCircuitAt, Circuit.eval_singleton,
    LinearMap.comp_apply]
  change (sitesEquivR R).symm
      ((recordReadoutGateAt R r).unitary ((sitesEquivR R) x)) =
    recordPhaseFlip (siteResolution R r) 1 x
  rw [show (recordReadoutGateAt R r).unitary =
    (sitesCell R r 1).reflection from rfl]
  change (sitesEquivR R).symm
      ((sitesCell R r 1).reflection ((sitesEquivR R) x)) =
    recordPhaseFlip (siteResolution R r) 1 x
  calc
    (sitesEquivR R).symm
        ((sitesCell R r 1).reflection ((sitesEquivR R) x)) =
        (siteCell R r 1).reflection x := by
      simpa [siteCell] using
        (Submodule.reflection_map_apply
          (sitesEquivR R).symm (sitesCell R r 1) x).symm
    _ = recordPhaseFlip (siteResolution R r) 1 x := by
      rw [Submodule.reflection_apply]
      simp [recordPhaseFlip, Gleason.projL, siteResolution]
      module

/-- The one-site reflection that reads the bit-one record at `firstSite`. -/
def recordReadoutGate (R : ℕ) [NeZero R] : TwoLocalGate R 2 :=
  recordReadoutGateAt R (firstSite R)

@[simp] theorem recordReadoutGate_support (R : ℕ) [NeZero R] :
    (recordReadoutGate R).support = {firstSite R} := rfl

@[simp] theorem recordReadoutGate_support_card (R : ℕ) [NeZero R] :
    (recordReadoutGate R).support.card = 1 := by simp

theorem recordReadoutGate_local (R : ℕ) [NeZero R] :
    IsLocalTo
      (recordReadoutGate R).unitary.toLinearIsometry.toLinearMap
      {firstSite R} :=
  (recordReadoutGate R).locality

/-- The constant-cost readout circuit consists of the single reflection gate. -/
def recordReadoutCircuit (R : ℕ) [NeZero R] : Circuit R 2 :=
  recordReadoutCircuitAt R (firstSite R)

@[simp] theorem recordReadoutCircuit_length (R : ℕ) [NeZero R] :
    (recordReadoutCircuit R).length = 1 := rfl

/-- The singleton circuit implements the exact abstract record phase flip.
Specialization of `recordReadoutCircuitAt_implements` at `firstSite`. -/
theorem recordReadoutCircuit_implements_phase_flip (R : ℕ) [NeZero R] :
    ImplementsRecordPhaseFlip
      (sitesEquivR R) (recordReadoutCircuit R)
      (repetitionRecords R (firstSite R)) 1 :=
  recordReadoutCircuitAt_implements R (firstSite R)

/-- The explicit readout distinguishes the two unit branches at threshold one. -/
theorem repetition_distinguishesAt_one (R : ℕ) [NeZero R] :
    DistinguishesAt (sitesEquivR R) (zeroBranch R) (oneBranch R) 1
      (recordReadoutCircuit R) := by
  simpa [normalized_repetition_branch_zero, normalized_repetition_branch_one] using
    record_phase_flip_distinguishesAt
      (sitesEquivR R) (repetitionRecords R) (repetitionState R)
      (repetitionState_isRecordedOn R) (firstSite R) 0 1 (by decide)
      (by simpa [repetition_branch_zero] using zeroBranch_ne_zero R)
      (by simpa [repetition_branch_one] using oneBranch_ne_zero R)
      1 (by norm_num) (by norm_num) (recordReadoutCircuit R)
      (recordReadoutCircuit_implements_phase_flip R)

/-- The supplied one-gate readout gives the concrete upper bound `C_D ≤ 1`. -/
theorem repetition_distinguishability_upper (R : ℕ) [NeZero R] :
    distinguishabilityComplexity
      (sitesEquivR R) (zeroBranch R) (oneBranch R) 1 ≤ (1 : WithTop ℕ) := by
  unfold distinguishabilityComplexity
  calc
    minCircuitLength (DistinguishesAt (sitesEquivR R) (zeroBranch R) (oneBranch R) 1)
        ≤ ((recordReadoutCircuit R).length : WithTop ℕ) :=
      minCircuitLength_le_of_witness
        (recordReadoutCircuit R) (repetition_distinguishesAt_one R)
    _ = 1 := by rw [recordReadoutCircuit_length]; rfl

#print axioms recordReadoutCircuit_implements_phase_flip

end

end QuantumFoundations.Complexity.RepetitionModel
