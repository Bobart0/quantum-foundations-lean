import QuantumFoundations.Complexity.ProxyDefs

/-!
# C3 — Relational proxy certificates

The physical statements are expressed first as per-circuit lower bounds and
explicit-witness upper bounds.  This layer deliberately precedes any
minimum-complexity construction.
-/

namespace QuantumFoundations.Complexity

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

/-- Every circuit satisfying the interference proxy has length at least
`B`. -/
def HasInterferenceLowerBound {N d : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N)) (δ : ℝ)
    (B : ℕ) : Prop :=
  ∀ C, InterferesAt e a b δ C → B ≤ Circuit.length C

/-- There is an explicit circuit satisfying the distinguishability proxy
whose length is at most `D`. -/
def HasDistinguishabilityUpperBound {N d : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N)) (δ : ℝ)
    (D : ℕ) : Prop :=
  ∃ C, Circuit.length C ≤ D ∧ DistinguishesAt e a b δ C

/-- A subtraction-free proxy-gap certificate: an interference lower bound
`B`, a distinguishability upper bound `D`, and `D + g ≤ B`. -/
def HasProxyGapAtLeast {N d : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N)) (δ : ℝ)
    (g : ℕ) : Prop :=
  ∃ B D,
    HasInterferenceLowerBound e a b δ B ∧
      HasDistinguishabilityUpperBound e a b δ D ∧
      D + g ≤ B

/-- Weakening a certified interference lower bound preserves it. -/
theorem HasInterferenceLowerBound.mono_bound {N d : ℕ}
    {e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d} {a b : H (d ^ N)} {δ : ℝ}
    {B B' : ℕ} (h : HasInterferenceLowerBound e a b δ B) (hB : B' ≤ B) :
    HasInterferenceLowerBound e a b δ B' := by
  intro C hC
  exact hB.trans (h C hC)

/-- Raising the interference threshold preserves a lower-bound certificate. -/
theorem HasInterferenceLowerBound.mono_threshold {N d : ℕ}
    {e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d} {a b : H (d ^ N)} {δ δ' : ℝ}
    {B : ℕ} (h : HasInterferenceLowerBound e a b δ B) (hδ : δ ≤ δ') :
    HasInterferenceLowerBound e a b δ' B := by
  intro C hC
  exact h C (interferesAt_mono_threshold hδ hC)

/-- Enlarging a distinguishability upper bound preserves its witness. -/
theorem HasDistinguishabilityUpperBound.mono_bound {N d : ℕ}
    {e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d} {a b : H (d ^ N)} {δ : ℝ}
    {D D' : ℕ} (h : HasDistinguishabilityUpperBound e a b δ D) (hD : D ≤ D') :
    HasDistinguishabilityUpperBound e a b δ D' := by
  obtain ⟨C, hlen, hC⟩ := h
  exact ⟨C, hlen.trans hD, hC⟩

/-- Lowering the distinguishability threshold preserves an upper-bound
witness. -/
theorem HasDistinguishabilityUpperBound.mono_threshold {N d : ℕ}
    {e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d} {a b : H (d ^ N)} {δ δ' : ℝ}
    {D : ℕ} (h : HasDistinguishabilityUpperBound e a b δ D) (hδ : δ' ≤ δ) :
    HasDistinguishabilityUpperBound e a b δ' D := by
  obtain ⟨C, hlen, hC⟩ := h
  exact ⟨C, hlen, distinguishesAt_mono_threshold hδ hC⟩

/-- Weakening the requested gap preserves a gap certificate. -/
theorem HasProxyGapAtLeast.mono {N d : ℕ}
    {e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d} {a b : H (d ^ N)} {δ : ℝ}
    {g g' : ℕ} (h : HasProxyGapAtLeast e a b δ g) (hg : g' ≤ g) :
    HasProxyGapAtLeast e a b δ g' := by
  obtain ⟨B, D, hI, hD, hgap⟩ := h
  refine ⟨B, D, hI, hD, ?_⟩
  omega

/-- The natural-number ceiling of `R / 2`. -/
def ceilHalf (R : ℕ) : ℕ := (R + 1) / 2

/-- Convert the division-free counting bound `R ≤ 2*k` into
`ceilHalf R ≤ k`. -/
theorem ceilHalf_le_of_le_two_mul {R k : ℕ} (h : R ≤ 2 * k) :
    ceilHalf R ≤ k := by
  unfold ceilHalf
  omega

end

end QuantumFoundations.Complexity
