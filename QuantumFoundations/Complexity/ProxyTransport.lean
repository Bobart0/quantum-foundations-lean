import QuantumFoundations.Complexity.CircuitInverse
import QuantumFoundations.Complexity.ProxyDefs

/-!
# C7b — Exact transport of branch-complexity proxies

Finite circuit evaluation preserves inner products exactly.  Combining this
unitarity with the two inverse identities in a reversible evolution transports
each underlying complex matrix element, hence both proxy predicates, without
approximation.
-/

namespace QuantumFoundations.Complexity

open scoped InnerProductSpace

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

namespace Circuit

/-- Every exact circuit preserves the complex inner product. -/
theorem eval_inner_map_map (C : Circuit N d) (x y : Sites N d) :
    ⟪eval C x, eval C y⟫_ℂ = ⟪x, y⟫_ℂ := by
  induction C generalizing x y with
  | nil => rfl
  | cons G C ih =>
      rw [eval_cons]
      change ⟪eval C (G.unitary x), eval C (G.unitary y)⟫_ℂ = _
      rw [ih, G.unitary.inner_map_map]

/-- Every exact circuit preserves norm on the site space. -/
theorem eval_norm (C : Circuit N d) (x : Sites N d) :
    ‖eval C x‖ = ‖x‖ := by
  induction C generalizing x with
  | nil => rfl
  | cons G C ih =>
      rw [eval_cons]
      change ‖eval C (G.unitary x)‖ = ‖x‖
      rw [ih, G.unitary.norm_map]

/-- Transported circuit evaluation preserves the complex inner product. -/
theorem evalOnH_inner_map_map (C : Circuit N d)
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (x y : H (d ^ N)) :
    ⟪evalOnH C e x, evalOnH C e y⟫_ℂ = ⟪x, y⟫_ℂ := by
  change ⟪e.symm (eval C (e x)), e.symm (eval C (e y))⟫_ℂ = _
  rw [e.symm.inner_map_map, eval_inner_map_map, e.inner_map_map]

/-- Transported circuit evaluation preserves norm. -/
theorem evalOnH_norm (C : Circuit N d)
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (x : H (d ^ N)) :
    ‖evalOnH C e x‖ = ‖x‖ := by
  change ‖e.symm (eval C (e x))‖ = ‖x‖
  rw [e.symm.norm_map, eval_norm, e.norm_map]

/-- Transported unitary circuit evaluation cannot annihilate a nonzero
vector. -/
theorem evalOnH_ne_zero (C : Circuit N d)
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) {x : H (d ^ N)} (hx : x ≠ 0) :
    evalOnH C e x ≠ 0 := by
  intro hzero
  apply hx
  apply norm_eq_zero.mp
  rw [← evalOnH_norm C e x, hzero, norm_zero]

/-- A unit vector remains a unit vector under finite circuit evolution. -/
theorem evalOnH_unit (C : Circuit N d)
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) {x : H (d ^ N)} (hx : ‖x‖ = 1) :
    ‖evalOnH C e x‖ = 1 := by
  rw [evalOnH_norm, hx]

end Circuit

namespace ReversibleCircuitEvolution

/-- Exact transport of a complex matrix element by push-forward conjugation. -/
theorem inner_evalOnH_pushForward (Evo : ReversibleCircuitEvolution N d)
    (C : Circuit N d) (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (x y : H (d ^ N)) :
    ⟪Circuit.evalOnH Evo.forward e x,
      Circuit.evalOnH (Evo.pushForward C) e
        (Circuit.evalOnH Evo.forward e y)⟫_ℂ =
      ⟪x, Circuit.evalOnH C e y⟫_ℂ := by
  rw [evalOnH_pushForward]
  have hcancel := congrArg
    (fun T : H (d ^ N) →ₗ[ℂ] H (d ^ N) => T y)
    (evalOnH_backward_forward Evo e)
  change Circuit.evalOnH Evo.backward e
      (Circuit.evalOnH Evo.forward e y) = y at hcancel
  change ⟪Circuit.evalOnH Evo.forward e x,
      Circuit.evalOnH Evo.forward e
        (Circuit.evalOnH C e
          (Circuit.evalOnH Evo.backward e
            (Circuit.evalOnH Evo.forward e y)))⟫_ℂ = _
  rw [hcancel]
  exact Circuit.evalOnH_inner_map_map Evo.forward e x
    (Circuit.evalOnH C e y)

/-- Exact transport of a complex matrix element by pullback conjugation. -/
theorem inner_evalOnH_pullBack (Evo : ReversibleCircuitEvolution N d)
    (C : Circuit N d) (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (x y : H (d ^ N)) :
    ⟪x, Circuit.evalOnH (Evo.pullBack C) e y⟫_ℂ =
      ⟪Circuit.evalOnH Evo.forward e x,
        Circuit.evalOnH C e (Circuit.evalOnH Evo.forward e y)⟫_ℂ := by
  rw [evalOnH_pullBack]
  have hcancel := congrArg
    (fun T : H (d ^ N) →ₗ[ℂ] H (d ^ N) =>
      T (Circuit.evalOnH C e (Circuit.evalOnH Evo.forward e y)))
    (evalOnH_forward_backward Evo e)
  change Circuit.evalOnH Evo.forward e
      (Circuit.evalOnH Evo.backward e
        (Circuit.evalOnH C e (Circuit.evalOnH Evo.forward e y))) =
      Circuit.evalOnH C e (Circuit.evalOnH Evo.forward e y) at hcancel
  calc
    _ = ⟪Circuit.evalOnH Evo.forward e x,
        Circuit.evalOnH Evo.forward e
          (Circuit.evalOnH Evo.backward e
            (Circuit.evalOnH C e (Circuit.evalOnH Evo.forward e y)))⟫_ℂ :=
      (Circuit.evalOnH_inner_map_map Evo.forward e x _).symm
    _ = _ := by rw [hcancel]

/-- Exact distinguishability-proxy invariance under push-forward
conjugation. -/
theorem distinguishesAt_pushForward_iff
    (Evo : ReversibleCircuitEvolution N d)
    (C : Circuit N d) (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (a b : H (d ^ N)) (δ : ℝ) :
    DistinguishesAt e a b δ C ↔
      DistinguishesAt e
        (Circuit.evalOnH Evo.forward e a)
        (Circuit.evalOnH Evo.forward e b) δ (Evo.pushForward C) := by
  unfold DistinguishesAt
  rw [inner_evalOnH_pushForward, inner_evalOnH_pushForward]

/-- Exact interference-proxy invariance under push-forward conjugation. -/
theorem interferesAt_pushForward_iff
    (Evo : ReversibleCircuitEvolution N d)
    (C : Circuit N d) (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (a b : H (d ^ N)) (δ : ℝ) :
    InterferesAt e a b δ C ↔
      InterferesAt e
        (Circuit.evalOnH Evo.forward e a)
        (Circuit.evalOnH Evo.forward e b) δ (Evo.pushForward C) := by
  unfold InterferesAt
  rw [inner_evalOnH_pushForward, inner_evalOnH_pushForward]

/-- Pulling an evolved-state distinguishing circuit back is equivalent to
its original evolved-state proxy. -/
theorem distinguishesAt_pullBack_iff
    (Evo : ReversibleCircuitEvolution N d)
    (C : Circuit N d) (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (a b : H (d ^ N)) (δ : ℝ) :
    DistinguishesAt e
        (Circuit.evalOnH Evo.forward e a)
        (Circuit.evalOnH Evo.forward e b) δ C ↔
      DistinguishesAt e a b δ (Evo.pullBack C) := by
  unfold DistinguishesAt
  rw [inner_evalOnH_pullBack, inner_evalOnH_pullBack]

/-- Pulling an evolved-state interference circuit back is equivalent to its
original evolved-state proxy. -/
theorem interferesAt_pullBack_iff
    (Evo : ReversibleCircuitEvolution N d)
    (C : Circuit N d) (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (a b : H (d ^ N)) (δ : ℝ) :
    InterferesAt e
        (Circuit.evalOnH Evo.forward e a)
        (Circuit.evalOnH Evo.forward e b) δ C ↔
      InterferesAt e a b δ (Evo.pullBack C) := by
  unfold InterferesAt
  rw [inner_evalOnH_pullBack, inner_evalOnH_pullBack]

end ReversibleCircuitEvolution

end

end QuantumFoundations.Complexity
