import QuantumFoundations.BranchesRiedel.BornBridge.RecordChoice

/-!
# C14b.1 — Active branch index

`B f` denotes a branch vector: for a joint branch family this is
`jointBranch Obs ψ f` (or `jointBranchWithChoice Obs choice ψ f`), but the
constructions in this file only use that `B : F → H n` is a function out of
a finite index type — nothing about records, redundancy, or Riedel's theorem
is used here. `ActiveBranchIndex B` restricts to the labels whose branch
vector is genuinely nonzero: a zero branch vector carries no formal cell (a
one-dimensional span of the zero vector is `⊥`, which `Perspective` excludes
by its `nz` field), even though its assigned Born weight will turn out to be
zero (`C14f`).
-/

namespace QuantumFoundations.BranchesRiedel.BornBridge

open scoped InnerProductSpace Classical
open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

variable {n : ℕ} {F : Type*} [Fintype F]

/-- The active branch index: labels `f` whose branch vector `B f` is
nonzero. A finite subtype of the finite index type `F`. -/
def ActiveBranchIndex (B : F → H n) := {f : F // B f ≠ 0}

noncomputable instance (B : F → H n) : Fintype (ActiveBranchIndex B) := Subtype.fintype _

theorem activeBranchIndex_finite (B : F → H n) : Finite (ActiveBranchIndex B) := inferInstance

/-- If `ψ ≠ 0` and the branch family reconstructs `ψ`, at least one branch
vector is nonzero, so the active branch index is nonempty. -/
theorem activeBranchIndex_nonempty (B : F → H n) {ψ : H n} (hψ : ψ ≠ 0)
    (hsum : ∑ f, B f = ψ) : Nonempty (ActiveBranchIndex B) := by
  by_contra hempty
  rw [not_nonempty_iff] at hempty
  apply hψ
  rw [← hsum]
  apply Finset.sum_eq_zero
  intro f _
  by_contra hf0
  exact hempty.false (⟨f, hf0⟩ : ActiveBranchIndex B)

/-- For a *normalized* state (`‖ψ‖ = 1`, hence `ψ ≠ 0`), nonemptiness of the
active branch index follows automatically. -/
theorem activeBranchIndex_nonempty_of_norm_eq_one (B : F → H n) {ψ : H n} (hψ : ‖ψ‖ = 1)
    (hsum : ∑ f, B f = ψ) : Nonempty (ActiveBranchIndex B) :=
  activeBranchIndex_nonempty B (by intro h; rw [h, norm_zero] at hψ; norm_num at hψ) hsum

/-- The active branch vector at an active index: literally `B` restricted
to `ActiveBranchIndex B`. -/
def activeBranchVector (B : F → H n) (f : ActiveBranchIndex B) : H n := B f.1

theorem activeBranchVector_ne_zero (B : F → H n) (f : ActiveBranchIndex B) :
    activeBranchVector B f ≠ 0 := f.2

/-- Summing over the full index type `F` and summing over only the active
indices give the same result: every inactive term is literally zero.
Reused by `C14d`'s `ψ_mem_branchSupport` and `C14f`'s normalization
theorem. -/
theorem sum_over_F_eq_sum_active (B : F → H n) {ψ : H n} (hsum : ∑ g : F, B g = ψ) :
    ∑ f : ActiveBranchIndex B, activeBranchVector B f = ψ := by
  rw [← hsum]
  have hkey := Fintype.sum_subtype_add_sum_subtype (fun f : F => B f ≠ 0) B
  have hzero : ∑ i : {x : F // ¬ (B x ≠ 0)}, B i.1 = 0 :=
    Finset.sum_eq_zero (fun i _ => not_not.mp i.2)
  rw [hzero, add_zero] at hkey
  exact hkey

end

end QuantumFoundations.BranchesRiedel.BornBridge
