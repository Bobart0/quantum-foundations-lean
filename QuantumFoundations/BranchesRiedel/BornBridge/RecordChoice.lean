import QuantumFoundations.BranchesRiedel.Local

/-!
# C14a — Redundant record-choice invariance

**Directory note.** The task specification names the target directory
`QuantumFoundations/Branches/BornBridge/` and namespace
`QuantumFoundations.Branches.BornBridge`. The repository's actual branch
module is `QuantumFoundations.BranchesRiedel` (there is no `Branches`
namespace); `BornBridge` is placed underneath it, following existing
convention, as `QuantumFoundations.BranchesRiedel.BornBridge`.

`Induction.lean`'s header explicitly flags that invariance of `jointBranch`
under an arbitrary choice of per-observable records `ρ : Fin A → Fin R` is
not stated there, and its "deviation" note worries that generalizing the
*eigenstate*/*uniqueness* property (`Induction.riedel`'s fourth conjunct,
which is stated relative to record `0` specifically) to an arbitrary record
would require composing two different records of the *same* observable at an
interior point of the chain, which `rproj_contract` does not cover.

That worry does not apply to the question actually asked here: whether
`chainProj`/`jointBranch` *itself* is invariant under the record-choice
function `ρ`. `Induction.tunneling` already proves exactly the needed
one-step substitution — for an observable `a` *not* occurring in the
already-processed list `L`, replacing its record leaves
`rproj (Obs a r) i (chainProj Obs L ρ f ψ)` unchanged, for *any* `ρ` used to
build the chain on `L`. Since `jointBranch`'s underlying list
`List.finRange A` has no duplicates, an induction that peels one observable
at a time from the *end* of the list always presents the newly-added
observable as absent from the (shorter) remaining list — precisely
`tunneling`'s hypothesis — so no interior composition of two records of the
same observable is ever required. Full simultaneous choice invariance
therefore follows from `tunneling` alone, by finite replacement one
observable at a time, exactly as the task recommends.
-/

namespace QuantumFoundations.BranchesRiedel.BornBridge

open scoped InnerProductSpace
open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

variable {n K R A : ℕ}

/-- A record-choice function: for every observable `a : Fin A`, a selected
record index in `Fin R`. Every record index is a *valid* selection (there is
no further validity predicate beyond membership in `Fin R`), so this is
exactly `Fin A → Fin R`, the same type `chainProj`/`Induction.tunneling`
already thread through as `ρ`. -/
abbrev RecordChoice (A R : ℕ) := Fin A → Fin R

/-- The joint branch of `ψ`, `f : Fin A → Fin K`, built using the records
selected by `choice` rather than the canonical record `0` of each
observable — otherwise exactly `jointBranch`'s own ordered-product
construction (`List.finRange A`, folded left to right). -/
def jointBranchWithChoice [NeZero R] (Obs : Fin A → Fin R → LabeledResolution n K)
    (choice : RecordChoice A R) (ψ : H n) (f : Fin A → Fin K) : H n :=
  chainProj Obs (List.finRange A) choice f ψ

theorem jointBranchWithChoice_canonical [NeZero R] (Obs : Fin A → Fin R → LabeledResolution n K)
    (ψ : H n) (f : Fin A → Fin K) :
    jointBranchWithChoice Obs (0 : RecordChoice A R) ψ f = jointBranch Obs ψ f := rfl

/-! ## C14a.0 — The general replacement mechanism -/

/-- **The general mechanism underlying every result in this file.** For any
two record-choice functions `ρ`, `ρ'`, the chain built over an arbitrary
nodup list `L` gives the same result, regardless of which of `ρ`/`ρ'`
selects the records. Proved by peeling `L` from the end: the newly exposed
observable at each step is always absent from the shorter remaining prefix
(by `L.Nodup`), which is exactly `tunneling`'s hypothesis, so each step is a
single reuse of `tunneling` — never composing two records of the same
observable at an interior point of the chain. -/
theorem chainProj_choice_invariant (Obs : Fin A → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs) :
    ∀ (L : List (Fin A)), L.Nodup → ∀ (ρ ρ' : Fin A → Fin R) (f : Fin A → Fin K),
      chainProj Obs L ρ f ψ = chainProj Obs L ρ' f ψ := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro _ ρ ρ' f; rfl
  | append_singleton L' b ih =>
    intro hnodup ρ ρ' f
    have hbL' : b ∉ L' := by
      intro hb
      exact (List.nodup_append.mp hnodup).2.2 b hb b (List.mem_singleton_self b) rfl
    have hL'nodup : L'.Nodup := (List.nodup_append.mp hnodup).1
    have hunfold : ∀ σ : Fin A → Fin R, chainProj Obs (L' ++ [b]) σ f ψ
        = rproj (Obs b (σ b)) (f b) (chainProj Obs L' σ f ψ) := fun σ =>
      List.foldl_concat _ ψ b L'
    rw [hunfold ρ, hunfold ρ']
    rw [ih hL'nodup ρ ρ' f]
    exact tunneling Obs ψ hrec hcw L' hL'nodup ρ' f b hbL' (ρ b) (ρ' b) (f b)

/-! ## C14a.1 — Single-observable replacement -/

/-- **Section 4.1.** Replacing the canonical record of a single observable
`a` (record `r` versus `r'`), holding every other observable at its
canonical record `0`, does not change the resulting joint branch. A direct
specialization of `chainProj_choice_invariant` at the two choice functions
`Function.update 0 a r` and `Function.update 0 a r'`, which differ only at
`a`. -/
theorem replace_one_record_preserves_joint_branch [NeZero R]
    (Obs : Fin A → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs)
    (a : Fin A) (r r' : Fin R) (f : Fin A → Fin K) :
    jointBranchWithChoice Obs (Function.update (0 : RecordChoice A R) a r) ψ f
      = jointBranchWithChoice Obs (Function.update (0 : RecordChoice A R) a r') ψ f :=
  chainProj_choice_invariant Obs ψ hrec hcw (List.finRange A) (List.nodup_finRange A)
    (Function.update (0 : RecordChoice A R) a r) (Function.update (0 : RecordChoice A R) a r') f

/-! ## C14a.2 — Full choice invariance -/

/-- **Section 4.2.** The joint branch built from an arbitrary record choice
`choice` coincides with the canonical joint branch (`ρ = 0`). -/
theorem jointBranchWithChoice_eq_jointBranch [NeZero R]
    (Obs : Fin A → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs)
    (choice : RecordChoice A R) (f : Fin A → Fin K) :
    jointBranchWithChoice Obs choice ψ f = jointBranch Obs ψ f :=
  chainProj_choice_invariant Obs ψ hrec hcw (List.finRange A) (List.nodup_finRange A) choice 0 f

/-- **Section 4.2.** Any two record choices yield the same joint branch. -/
theorem jointBranchWithChoice_independent [NeZero R]
    (Obs : Fin A → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs)
    (choice choice' : RecordChoice A R) (f : Fin A → Fin K) :
    jointBranchWithChoice Obs choice ψ f = jointBranchWithChoice Obs choice' ψ f :=
  chainProj_choice_invariant Obs ψ hrec hcw (List.finRange A) (List.nodup_finRange A)
    choice choice' f

/-! ## C14a.3 — Choice-independent decomposition -/

/-- **Section 4.3.** Reconstruction of `ψ` holds for every selected-record
presentation, by rewriting to the canonical family. -/
theorem jointBranchWithChoice_sum [NeZero R] [NeZero K]
    (Obs : Fin A → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs) (choice : RecordChoice A R) :
    ∑ f : Fin A → Fin K, jointBranchWithChoice Obs choice ψ f = ψ := by
  simp_rw [jointBranchWithChoice_eq_jointBranch Obs ψ hrec hcw choice]
  exact jointBranch_sum Obs ψ

/-- **Section 4.3.** Pairwise orthogonality holds for every selected-record
presentation. -/
theorem jointBranchWithChoice_orthogonal [NeZero R]
    (Obs : Fin A → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs) (choice : RecordChoice A R)
    {f f' : Fin A → Fin K} (hff : f ≠ f') :
    ⟪jointBranchWithChoice Obs choice ψ f, jointBranchWithChoice Obs choice ψ f'⟫_ℂ = 0 := by
  rw [jointBranchWithChoice_eq_jointBranch Obs ψ hrec hcw choice,
    jointBranchWithChoice_eq_jointBranch Obs ψ hrec hcw choice]
  exact jointBranch_orthogonal Obs ψ hrec hcw hff

/-- **Section 4.3.** The simultaneous-eigenvector property (relative to
record `0` of each observable, as in `Induction.riedel`) holds for every
selected-record presentation. -/
theorem jointBranchWithChoice_eigen [NeZero R]
    (Obs : Fin A → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs) (choice : RecordChoice A R)
    (f : Fin A → Fin K) (k : Fin K) (a : Fin A) :
    rproj (Obs a 0) k (jointBranchWithChoice Obs choice ψ f)
      = (if k = f a then (1 : ℂ) else 0) • jointBranchWithChoice Obs choice ψ f := by
  rw [jointBranchWithChoice_eq_jointBranch Obs ψ hrec hcw choice]
  exact diagonal Obs ψ hrec hcw (List.finRange A) (List.nodup_finRange A) 0 f a
    (List.mem_finRange a) k

/-- **Section 4.3.** Uniqueness: any reconstruction satisfying the
simultaneous-eigenvector property agrees with every selected-record
presentation of the joint branch. -/
theorem jointBranchWithChoice_unique [NeZero R] [NeZero K]
    (Obs : Fin A → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs) (choice : RecordChoice A R)
    (w : (Fin A → Fin K) → H n) (hsum : ∑ f : Fin A → Fin K, w f = ψ)
    (heig : ∀ (f : Fin A → Fin K) (a : Fin A) (k : Fin K),
      rproj (Obs a 0) k (w f) = (if k = f a then (1 : ℂ) else 0) • w f)
    (f : Fin A → Fin K) : w f = jointBranchWithChoice Obs choice ψ f := by
  rw [jointBranchWithChoice_eq_jointBranch Obs ψ hrec hcw choice]
  exact (riedel Obs ψ hrec hcw).2.2.2 w hsum heig f

/-- **Section 4.3, local corollary.** In the finite multisite model, under
pairwise non-pair-covering of the observable supports (the same hypotheses
as `riedel_local`), reconstruction and orthogonality hold for every
selected-record presentation as well. -/
theorem jointBranchWithChoice_local {N d : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (Obs : Fin A → Fin R → LabeledResolution (d ^ N) K)
    (supp : Fin A → Fin R → Finset (Fin N)) [NeZero R] [NeZero K] (hR2 : 2 ≤ R)
    (ψ : H (d ^ N)) (hrec : ∀ a, IsRecordedOn ψ (Obs a))
    (hlocal : ∀ a r i, IsLocalTo
      (e.toLinearIsometry.toLinearMap ∘ₗ rproj (Obs a r) i ∘ₗ e.symm.toLinearIsometry.toLinearMap)
      (supp a r))
    (hnpc : ∀ a b : Fin A, a ≠ b → ¬ PairCovers (supp a) (supp b)) (choice : RecordChoice A R) :
    (∑ f : Fin A → Fin K, jointBranchWithChoice Obs choice ψ f = ψ) ∧
    (∀ f f' : Fin A → Fin K, f ≠ f' →
      ⟪jointBranchWithChoice Obs choice ψ f, jointBranchWithChoice Obs choice ψ f'⟫_ℂ = 0) :=
  let hcw := commuteWitness_of_not_pairCovers e Obs supp hR2 hlocal hnpc
  ⟨jointBranchWithChoice_sum Obs ψ hrec hcw choice,
    fun f f' hff => jointBranchWithChoice_orthogonal Obs ψ hrec hcw choice hff⟩

end

end QuantumFoundations.BranchesRiedel.BornBridge
