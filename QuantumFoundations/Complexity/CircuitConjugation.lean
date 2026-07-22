import QuantumFoundations.Complexity.RecordInterference

/-!
# C7a — Reversible circuit evolution and conjugation

The general persistence layer records separate forward and backward circuits
whose evaluations are mutual inverses.  It does not depend on constructing a
canonical inverse gate.

Because `Circuit.eval (C ++ D) = Circuit.eval D ∘ₗ Circuit.eval C`, the list
`backward ++ C ++ forward` implements `forward ∘ C ∘ backward`, whereas
`forward ++ C ++ backward` implements `backward ∘ C ∘ forward`.
-/

namespace QuantumFoundations.Complexity

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

/-- A finite unitary evolution together with an explicit inverse circuit. -/
structure ReversibleCircuitEvolution (N d : ℕ) where
  forward : Circuit N d
  backward : Circuit N d
  backward_forward :
    Circuit.eval backward ∘ₗ Circuit.eval forward = LinearMap.id
  forward_backward :
    Circuit.eval forward ∘ₗ Circuit.eval backward = LinearMap.id

namespace ReversibleCircuitEvolution

/-- Total reversible conjugation overhead. -/
def overhead (Evo : ReversibleCircuitEvolution N d) : ℕ :=
  Circuit.length Evo.forward + Circuit.length Evo.backward

/-- The empty circuit in both directions is a concrete reversible evolution. -/
def reversibleEmptyEvolution (N d : ℕ) : ReversibleCircuitEvolution N d where
  forward := []
  backward := []
  backward_forward := by
    ext x
    rfl
  forward_backward := by
    ext x
    rfl

@[simp] theorem reversibleEmptyEvolution_overhead :
    (reversibleEmptyEvolution N d).overhead = 0 := rfl

/-- Push a circuit forward through the evolution: this list implements
`forward ∘ C ∘ backward`. -/
def pushForward (Evo : ReversibleCircuitEvolution N d) (C : Circuit N d) :
    Circuit N d :=
  Evo.backward ++ C ++ Evo.forward

/-- Pull a circuit back through the evolution: this list implements
`backward ∘ C ∘ forward`. -/
def pullBack (Evo : ReversibleCircuitEvolution N d) (C : Circuit N d) :
    Circuit N d :=
  Evo.forward ++ C ++ Evo.backward

theorem pushForward_length (Evo : ReversibleCircuitEvolution N d)
    (C : Circuit N d) :
    Circuit.length (Evo.pushForward C) =
      Circuit.length Evo.forward + Circuit.length C + Circuit.length Evo.backward := by
  simp [pushForward, Circuit.length]
  omega

theorem pullBack_length (Evo : ReversibleCircuitEvolution N d)
    (C : Circuit N d) :
    Circuit.length (Evo.pullBack C) =
      Circuit.length Evo.backward + Circuit.length C + Circuit.length Evo.forward := by
  simp [pullBack, Circuit.length]
  omega

theorem pushForward_length_eq (Evo : ReversibleCircuitEvolution N d)
    (C : Circuit N d) :
    Circuit.length (Evo.pushForward C) = Circuit.length C + Evo.overhead := by
  rw [pushForward_length]
  unfold overhead
  omega

theorem pullBack_length_eq (Evo : ReversibleCircuitEvolution N d)
    (C : Circuit N d) :
    Circuit.length (Evo.pullBack C) = Circuit.length C + Evo.overhead := by
  rw [pullBack_length]
  unfold overhead
  omega

/-- Site-space semantics of push-forward conjugation. -/
theorem eval_pushForward (Evo : ReversibleCircuitEvolution N d)
    (C : Circuit N d) :
    Circuit.eval (Evo.pushForward C) =
      Circuit.eval Evo.forward ∘ₗ Circuit.eval C ∘ₗ Circuit.eval Evo.backward := by
  rw [pushForward, Circuit.eval_append, Circuit.eval_append]

/-- Site-space semantics of pullback conjugation. -/
theorem eval_pullBack (Evo : ReversibleCircuitEvolution N d)
    (C : Circuit N d) :
    Circuit.eval (Evo.pullBack C) =
      Circuit.eval Evo.backward ∘ₗ Circuit.eval C ∘ₗ Circuit.eval Evo.forward := by
  rw [pullBack, Circuit.eval_append, Circuit.eval_append]

/-- The transported backward circuit is a left inverse of the transported
forward circuit. -/
theorem evalOnH_backward_forward (Evo : ReversibleCircuitEvolution N d)
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) :
    Circuit.evalOnH Evo.backward e ∘ₗ Circuit.evalOnH Evo.forward e =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply e.injective
  have h := congrArg (fun T : Sites N d →ₗ[ℂ] Sites N d => T (e x))
    Evo.backward_forward
  simpa [Circuit.evalOnH] using h

/-- The transported forward circuit is a left inverse of the transported
backward circuit. -/
theorem evalOnH_forward_backward (Evo : ReversibleCircuitEvolution N d)
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) :
    Circuit.evalOnH Evo.forward e ∘ₗ Circuit.evalOnH Evo.backward e =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply e.injective
  have h := congrArg (fun T : Sites N d →ₗ[ℂ] Sites N d => T (e x))
    Evo.forward_backward
  simpa [Circuit.evalOnH] using h

/-- Hilbert-space semantics of push-forward conjugation. -/
theorem evalOnH_pushForward (Evo : ReversibleCircuitEvolution N d)
    (C : Circuit N d) (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) :
    Circuit.evalOnH (Evo.pushForward C) e =
      Circuit.evalOnH Evo.forward e ∘ₗ Circuit.evalOnH C e ∘ₗ
        Circuit.evalOnH Evo.backward e := by
  apply LinearMap.ext
  intro x
  apply e.injective
  simp [Circuit.evalOnH, eval_pushForward]

/-- Hilbert-space semantics of pullback conjugation. -/
theorem evalOnH_pullBack (Evo : ReversibleCircuitEvolution N d)
    (C : Circuit N d) (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) :
    Circuit.evalOnH (Evo.pullBack C) e =
      Circuit.evalOnH Evo.backward e ∘ₗ Circuit.evalOnH C e ∘ₗ
        Circuit.evalOnH Evo.forward e := by
  apply LinearMap.ext
  intro x
  apply e.injective
  simp [Circuit.evalOnH, eval_pullBack]

end ReversibleCircuitEvolution

end

end QuantumFoundations.Complexity
