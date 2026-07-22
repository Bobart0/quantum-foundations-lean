import QuantumFoundations.Complexity.ProxyCertificates

/-!
# C13d — Threshold-margin proxy-gap certificates

`HasProxyGapMarginAtLeast e a b δ μ g` is the exact `HasProxyGapAtLeast`
certificate architecture (an interference lower bound, a distinguishability
upper bound, and a subtraction-free length separation `g`), except the two
proxies are required at the two *shifted* thresholds `δ - μ` (interference)
and `δ + μ` (distinguishability) instead of both at `δ`. At `μ = 0` this is
exactly `HasProxyGapAtLeast e a b δ g` (`margin_zero_iff_proxy_gap`).

Increasing `μ` moves the two thresholds in *opposite* directions — the
interference threshold `δ - μ` shrinks (a *harder* lower-bound target: more
circuits satisfy `InterferesAt` at smaller thresholds, so ruling all of them
out is harder) while the distinguishability threshold `δ + μ` grows (a
*harder* witness target: fewer circuits satisfy `DistinguishesAt` at larger
thresholds, so exhibiting one is harder). A margin certificate at `μ`
therefore does **not** get easier as `μ` grows; the only valid monotonicity
direction is the reverse: a certificate proved at a wide margin `μ`
automatically gives one at any narrower margin `μ' ≤ μ`, since each
individual proxy's own threshold-monotonicity (`HasInterferenceLowerBound.mono_threshold`
increasing, `HasDistinguishabilityUpperBound.mono_threshold` decreasing)
moves `δ - μ ≤ δ - μ'` and `δ + μ' ≤ δ + μ` in exactly the directions each
needs.
-/

namespace QuantumFoundations.Complexity.SimulatedEvolution

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity

noncomputable section

/-! ## C13d.1 — The margin-separated certificate -/

/-- A subtraction-free proxy-gap certificate at the central threshold `δ`
with margin `μ`: interference is lower-bounded at `δ - μ`, distinguishability
is upper-bounded at `δ + μ`, and the two circuit-length bounds are separated
by at least `g`. -/
def HasProxyGapMarginAtLeast {N d : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N)) (δ μ : ℝ)
    (g : ℕ) : Prop :=
  ∃ B D,
    HasInterferenceLowerBound e a b (δ - μ) B ∧
      HasDistinguishabilityUpperBound e a b (δ + μ) D ∧
      D + g ≤ B

namespace HasProxyGapMarginAtLeast

variable {N d : ℕ} {e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d} {a b : H (d ^ N)}
  {δ μ : ℝ} {g : ℕ}

/-- Weakening the requested gap preserves a margin certificate. -/
theorem mono_gap {g' : ℕ} (h : HasProxyGapMarginAtLeast e a b δ μ g)
    (hg : g' ≤ g) : HasProxyGapMarginAtLeast e a b δ μ g' := by
  obtain ⟨B, D, hI, hD, hbudget⟩ := h
  exact ⟨B, D, hI, hD, by omega⟩

/-- The only mathematically valid margin monotonicity: a certificate proved
at a wide margin `μ` gives one at any narrower margin `μ' ≤ μ` for free. A
*larger* margin is not automatically easier — see the module docstring. -/
theorem mono_margin {μ' : ℝ} (h : HasProxyGapMarginAtLeast e a b δ μ g)
    (hle : μ' ≤ μ) : HasProxyGapMarginAtLeast e a b δ μ' g := by
  obtain ⟨B, D, hI, hD, hbudget⟩ := h
  refine ⟨B, D, ?_, ?_, hbudget⟩
  · exact hI.mono_threshold (by linarith)
  · exact hD.mono_threshold (by linarith)

end HasProxyGapMarginAtLeast

/-! ## C13d.2 — Zero-margin regression -/

/-- At zero margin, the margin certificate is exactly the ordinary
central-threshold proxy gap. -/
theorem margin_zero_iff_proxy_gap {N d : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N)) (δ : ℝ) (g : ℕ) :
    HasProxyGapMarginAtLeast e a b δ 0 g ↔ HasProxyGapAtLeast e a b δ g := by
  unfold HasProxyGapMarginAtLeast HasProxyGapAtLeast
  simp

#print axioms HasProxyGapMarginAtLeast.mono_margin
#print axioms margin_zero_iff_proxy_gap

end

end QuantumFoundations.Complexity.SimulatedEvolution
