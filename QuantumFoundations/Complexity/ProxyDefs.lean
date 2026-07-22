import QuantumFoundations.Complexity.RecordInterference

/-!
# C3 — Exact circuit proxy predicates

This file defines the division-free Taylor–McCulloch proxy inequalities for
finite exact circuits.  Normalization is deliberately kept out of the
definitions: later theorems state the hypotheses under which their input
vectors are unit vectors.
-/

namespace QuantumFoundations.Complexity

open scoped InnerProductSpace

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

/-- A circuit distinguishes `a` from `b` at threshold `δ` when the norm of
the difference of its two diagonal matrix elements is at least `2 * δ`. -/
def DistinguishesAt {N d : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N)) (δ : ℝ)
    (C : Circuit N d) : Prop :=
  2 * δ ≤
    ‖⟪a, Circuit.evalOnH C e a⟫_ℂ -
      ⟪b, Circuit.evalOnH C e b⟫_ℂ‖

/-- A circuit interferes `a` and `b` at threshold `δ` when the sum of the
norms of its two cross matrix elements is at least `2 * δ`. -/
def InterferesAt {N d : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N)) (δ : ℝ)
    (C : Circuit N d) : Prop :=
  2 * δ ≤
    ‖⟪a, Circuit.evalOnH C e b⟫_ℂ‖ +
      ‖⟪b, Circuit.evalOnH C e a⟫_ℂ‖

/-- Lowering the threshold preserves distinguishability. -/
theorem distinguishesAt_mono_threshold {N d : ℕ}
    {e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d} {a b : H (d ^ N)} {δ δ' : ℝ}
    {C : Circuit N d} (hδ : δ' ≤ δ) (h : DistinguishesAt e a b δ C) :
    DistinguishesAt e a b δ' C := by
  unfold DistinguishesAt at h ⊢
  linarith

/-- Lowering the threshold preserves interference. -/
theorem interferesAt_mono_threshold {N d : ℕ}
    {e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d} {a b : H (d ^ N)} {δ δ' : ℝ}
    {C : Circuit N d} (hδ : δ' ≤ δ) (h : InterferesAt e a b δ C) :
    InterferesAt e a b δ' C := by
  unfold InterferesAt at h ⊢
  linarith

/-- At a positive threshold, two vanishing cross amplitudes rule out the
interference proxy.  Positivity is necessary: threshold zero is automatic. -/
theorem not_interferesAt_of_both_cross_amplitudes_zero {N d : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N)) (δ : ℝ)
    (C : Circuit N d) (hδ : 0 < δ)
    (hab : ⟪a, Circuit.evalOnH C e b⟫_ℂ = 0)
    (hba : ⟪b, Circuit.evalOnH C e a⟫_ℂ = 0) :
    ¬ InterferesAt e a b δ C := by
  intro h
  unfold InterferesAt at h
  rw [hab, hba, norm_zero, add_zero] at h
  linarith

/-- A positive-threshold interference certificate has at least one nonzero
cross amplitude. -/
theorem one_cross_amplitude_ne_zero_of_interferesAt {N d : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N)) (δ : ℝ)
    (C : Circuit N d) (hδ : 0 < δ) (h : InterferesAt e a b δ C) :
    ⟪a, Circuit.evalOnH C e b⟫_ℂ ≠ 0 ∨
      ⟪b, Circuit.evalOnH C e a⟫_ℂ ≠ 0 := by
  by_contra hzero
  push Not at hzero
  exact not_interferesAt_of_both_cross_amplitudes_zero
    e a b δ C hδ hzero.1 hzero.2 h

end

end QuantumFoundations.Complexity
