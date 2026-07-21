import QuantumFoundations.Complexity.CircuitLocality

/-!
# C1 — Untouched records kill cross amplitudes

This file bridges circuits on `Branches.Sites N d` to Riedel's branch
vectors on `Gleason.H (d ^ N)` through an explicit linear isometry.  It then
uses only the existing record-projector identities and self-adjointness.
-/

namespace QuantumFoundations.Complexity

open scoped InnerProductSpace

open Gleason
open QuantumFoundations.Branches

noncomputable section

namespace Circuit

/-- Evaluate a site circuit on `H (d ^ N)` through the chosen tensor-site identification. -/
def evalOnH (C : Circuit N d) (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) :
    H (d ^ N) →ₗ[ℂ] H (d ^ N) :=
  e.symm.toLinearIsometry.toLinearMap ∘ₗ eval C ∘ₗ e.toLinearIsometry.toLinearMap

end Circuit

/-- Transport a record projector from `H (d ^ N)` to the site representation. -/
def transportedRecordProj (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (Λ : LabeledResolution (d ^ N) K) (i : Fin K) : Sites N d →ₗ[ℂ] Sites N d :=
  e.toLinearIsometry.toLinearMap ∘ₗ rproj Λ i ∘ₗ e.symm.toLinearIsometry.toLinearMap

/-- A target-label record projector annihilates a distinct source branch. -/
theorem rproj_branch_eq_zero {N d K R : ℕ} [NeZero R]
    (recs : Fin R → LabeledResolution (d ^ N) K) (ψ : H (d ^ N))
    (hrec : IsRecordedOn ψ recs) (r : Fin R) (i j : Fin K) (hij : i ≠ j) :
    rproj (recs r) j (branch recs ψ i) = 0 := by
  rw [branch_wellDefined ψ recs hrec r i,
    rproj_contract_apply (recs r) j i ψ, if_neg (Ne.symm hij)]
  simp

/-- A target-label record projector fixes its own branch. -/
theorem rproj_branch_eq_self {N d K R : ℕ} [NeZero R]
    (recs : Fin R → LabeledResolution (d ^ N) K) (ψ : H (d ^ N))
    (hrec : IsRecordedOn ψ recs) (r : Fin R) (j : Fin K) :
    rproj (recs r) j (branch recs ψ j) = branch recs ψ j := by
  rw [branch_wellDefined ψ recs hrec r j,
    rproj_contract_apply (recs r) j j ψ, if_pos rfl]
  simp

/--
If the transported record projector is local to a region disjoint from the
circuit support, the circuit transported back to `H (d ^ N)` commutes with
that projector.
-/
theorem evalOnH_commute_recordProj (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (C : Circuit N d) (F : Finset (Fin N))
    (Λ : LabeledResolution (d ^ N) K) (j : Fin K)
    (hlocal : IsLocalTo (transportedRecordProj e Λ j) F)
    (hdisj : Disjoint (Circuit.support C) F) :
    Commute (Circuit.evalOnH C e) (rproj Λ j) := by
  have hsites : Commute (Circuit.eval C) (transportedRecordProj e Λ j) :=
    Circuit.circuit_commute_of_disjoint C F (transportedRecordProj e Λ j) hlocal hdisj
  apply LinearMap.ext
  intro x
  apply e.injective
  have hpoint := congrArg (fun T : Sites N d →ₗ[ℂ] Sites N d => T (e x)) hsites
  simpa [Circuit.evalOnH, transportedRecordProj] using hpoint

/--
An exact record on a region untouched by the circuit forces the matrix
element between two distinct recorded branches to vanish.
-/
theorem cross_amplitude_eq_zero_of_untouched_record {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (C : Circuit N d)
    (recs : Fin R → LabeledResolution (d ^ N) K) (ψ : H (d ^ N))
    (hrec : IsRecordedOn ψ recs) (r : Fin R) (F : Finset (Fin N))
    (i j : Fin K) (hij : i ≠ j)
    (hlocal : IsLocalTo (transportedRecordProj e (recs r) j) F)
    (hdisj : Disjoint (Circuit.support C) F) :
    ⟪branch recs ψ j, Circuit.evalOnH C e (branch recs ψ i)⟫_ℂ = 0 := by
  let P := rproj (recs r) j
  let V := Circuit.evalOnH C e
  have hcomm : Commute V P :=
    evalOnH_commute_recordProj e C F (recs r) j hlocal hdisj
  have htarget : P (branch recs ψ j) = branch recs ψ j :=
    rproj_branch_eq_self recs ψ hrec r j
  have hsource : P (branch recs ψ i) = 0 :=
    rproj_branch_eq_zero recs ψ hrec r i j hij
  have hsymm : LinearMap.IsSymmetric P := by
    intro x y
    exact Submodule.starProjection_isSymmetric ((recs r).cells j) x y
  change ⟪branch recs ψ j, V (branch recs ψ i)⟫_ℂ = 0
  calc
    ⟪branch recs ψ j, V (branch recs ψ i)⟫_ℂ =
        ⟪P (branch recs ψ j), V (branch recs ψ i)⟫_ℂ := by rw [htarget]
    _ = ⟪branch recs ψ j, P (V (branch recs ψ i))⟫_ℂ :=
      hsymm _ _
    _ = ⟪branch recs ψ j, V (P (branch recs ψ i))⟫_ℂ := by
      rw [commute_apply hcomm]
    _ = 0 := by rw [hsource, map_zero, inner_zero_right]

/--
Contrapositive form: a nonzero cross amplitude forces the circuit's union
support to touch the chosen record region.
-/
theorem touched_of_cross_amplitude_ne_zero {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (C : Circuit N d)
    (recs : Fin R → LabeledResolution (d ^ N) K) (ψ : H (d ^ N))
    (hrec : IsRecordedOn ψ recs) (r : Fin R) (F : Finset (Fin N))
    (i j : Fin K) (hij : i ≠ j)
    (hlocal : IsLocalTo (transportedRecordProj e (recs r) j) F)
    (hcross : ⟪branch recs ψ j, Circuit.evalOnH C e (branch recs ψ i)⟫_ℂ ≠ 0) :
    ¬ Disjoint (Circuit.support C) F := by
  intro hdisj
  exact hcross (cross_amplitude_eq_zero_of_untouched_record
    e C recs ψ hrec r F i j hij hlocal hdisj)

end

end QuantumFoundations.Complexity
