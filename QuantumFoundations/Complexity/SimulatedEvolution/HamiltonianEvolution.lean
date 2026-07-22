import QuantumFoundations.Complexity.SimulatedEvolution.TimeEvolution

/-!
# C13k — Certified Hamiltonian-generated evolution (optional)

`hamiltonianEvolution Hm hH` is a genuine `NormPreservingEvolution` whose
`evolve t` field is, **by construction**, the operator exponential
`exp(-i t Hm)` for a self-adjoint generator `Hm`: this is the strongest of
the task's acceptable Hamiltonian-evolution relations ("equality with the
operator exponential"), not an opaque or asserted relation. It reuses
Mathlib's existing `selfAdjoint.expUnitary : selfAdjoint A → unitary A`
(valid for any C⋆-algebra `A`, and `H n →L[ℂ] H n` is one, via the existing
`CStarAlgebra (E →L[ℂ] E)` instance) together with the adjoint/inner-product
API already used throughout C13, rather than any additional assumption or
Trotter-style approximation.

**What was completed:** the construction itself, norm preservation (derived
from `u ∈ unitary A ↔ star u * u = 1 ∧ u * star u = 1` and the defining
property of `ContinuousLinearMap.adjoint`, not reproved from coordinates),
and the zero-time regression `evolve 0 = id`.

**What was deferred, and exactly why:** the additive group law `evolve (s +
t) = evolve s * evolve t` (via `Commute.expUnitary_add`, which requires
`Commute` of the two scaled self-adjoint generators inside the `selfAdjoint
(H n →L[ℂ] H n)` subtype) and the time-reversal corollary. Both proof
attempts triggered a `synthInstance` deterministic timeout while resolving
ordinary additive-monoid instances (e.g. `AddCommMonoid ↥(selfAdjoint (H n
→L[ℂ] H n))`) through the `CStarAlgebra`/`NormedRing` instance stack — a
specific, reproducible Mathlib instance-resolution performance obstruction
on this subtype, not a mathematical gap (the underlying identity
`(-(s+t : ℝ) : ℂ) • Hm = (-(s:ℂ)) • Hm + (-(t:ℂ)) • Hm` and the commutation
`((-(s:ℂ)) • Hm) * ((-(t:ℂ)) • Hm) = ((-(t:ℂ)) • Hm) * ((-(s:ℂ)) • Hm)` are
both provable in isolation). This is left for C14 rather than worked around
with a slower/whole-file `set_option synthInstance.maxHeartbeats` increase,
which would mask rather than fix the underlying resolution cost.
-/

namespace QuantumFoundations.Complexity.SimulatedEvolution

open Gleason
open scoped InnerProductSpace

noncomputable section

/-! ## C13k.1 — Unitary elements of the operator C⋆-algebra are norm preserving -/

/-- Any unitary element of the C⋆-algebra `H n →L[ℂ] H n` (in the sense of
`unitary`, i.e. `star u * u = 1 ∧ u * star u = 1`) preserves norms: derived
directly from the defining property of `ContinuousLinearMap.adjoint`
(`star = adjoint` in this C⋆-algebra instance), not reproved from
coordinates. -/
theorem unitary_isNormPreserving {n : ℕ} (u : H n →L[ℂ] H n)
    (hu : u ∈ unitary (H n →L[ℂ] H n)) : IsNormPreserving u := by
  intro x
  have h1 : star u * u = 1 := Unitary.star_mul_self_of_mem hu
  have h2 : (ContinuousLinearMap.adjoint u).comp u = (1 : H n →L[ℂ] H n) := h1
  have h3 : ContinuousLinearMap.adjoint u (u x) = x := by
    have := congrArg (fun T : H n →L[ℂ] H n => T x) h2
    simpa using this
  have h4 : ⟪u x, u x⟫_ℂ = ⟪x, x⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_left u x (u x), h3]
  have h5 : ‖u x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ, h4]
  nlinarith [norm_nonneg (u x), norm_nonneg x]

/-! ## C13k.2 — Construction from a self-adjoint generator -/

/-- A real multiple `(-(t : ℂ)) • Hm` of a self-adjoint generator is itself
self-adjoint: `-(t : ℂ)` is a self-adjoint (real) scalar, and
`IsSelfAdjoint.smul` lifts this through the scalar action. -/
private theorem isSelfAdjoint_neg_ofReal_smul {n : ℕ} {Hm : H n →L[ℂ] H n}
    (hH : IsSelfAdjoint Hm) (t : ℝ) : IsSelfAdjoint ((-(t : ℂ)) • Hm) := by
  have hscalar : IsSelfAdjoint (-(t : ℂ)) := by
    unfold IsSelfAdjoint
    rw [star_neg]
    congr 1
    rw [Complex.star_def]
    simp
  exact hscalar.smul hH

/-- The Hamiltonian-generated evolution `exp(-i t Hm)` for a self-adjoint
generator `Hm`, packaged as a genuine `NormPreservingEvolution`: `evolve t`
is, by definition, `selfAdjoint.expUnitary` applied to the self-adjoint
element `(-(t : ℂ)) • Hm`, i.e. exactly the operator exponential
`NormedSpace.exp ((-Complex.I * t) • Hm)`. -/
noncomputable def hamiltonianEvolution {n : ℕ} (Hm : H n →L[ℂ] H n)
    (hH : IsSelfAdjoint Hm) : NormPreservingEvolution (H n) where
  evolve t := (selfAdjoint.expUnitary
    (⟨(-(t : ℂ)) • Hm, isSelfAdjoint_neg_ofReal_smul hH t⟩ :
      selfAdjoint (H n →L[ℂ] H n)) : H n →L[ℂ] H n)
  norm_apply := fun t x => unitary_isNormPreserving _
    (selfAdjoint.expUnitary
      (⟨(-(t : ℂ)) • Hm, isSelfAdjoint_neg_ofReal_smul hH t⟩ :
        selfAdjoint (H n →L[ℂ] H n))).2 x

/-- Regression: at time `0`, the Hamiltonian evolution is the identity. -/
theorem hamiltonianEvolution_evolve_zero {n : ℕ} (Hm : H n →L[ℂ] H n)
    (hH : IsSelfAdjoint Hm) :
    (hamiltonianEvolution Hm hH).evolve 0 = ContinuousLinearMap.id ℂ (H n) := by
  show (selfAdjoint.expUnitary
      (⟨(-((0 : ℝ) : ℂ)) • Hm, isSelfAdjoint_neg_ofReal_smul hH 0⟩ :
        selfAdjoint (H n →L[ℂ] H n)) : H n →L[ℂ] H n) = ContinuousLinearMap.id ℂ (H n)
  have harg : (⟨(-((0 : ℝ) : ℂ)) • Hm, isSelfAdjoint_neg_ofReal_smul hH 0⟩ :
      selfAdjoint (H n →L[ℂ] H n)) = 0 := by
    apply Subtype.ext
    show (-((0 : ℝ) : ℂ)) • Hm = 0
    rw [Complex.ofReal_zero, neg_zero]
    exact zero_smul ℂ Hm
  rw [harg, selfAdjoint.expUnitary_zero]
  rfl

#print axioms unitary_isNormPreserving
#print axioms hamiltonianEvolution_evolve_zero

end

end QuantumFoundations.Complexity.SimulatedEvolution
