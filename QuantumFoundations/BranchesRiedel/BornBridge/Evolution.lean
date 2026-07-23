import QuantumFoundations.BranchesRiedel.BornBridge.GeneratedBranches
import QuantumFoundations.Complexity.SimulatedEvolution.NoisyRepetition

/-!
# C14k — Preservation of branch weights under norm-preserving evolution

Connects `C13`'s `NormPreservingEvolution` to the branch-cell/Born-weight
machinery of `C14a`–`C14j`. The evolved branches `U.evolve t (B f)` are
*not* claimed to be selected by the original record projectors — a
norm-preserving evolution need not commute with any particular record — so
this file establishes only the invariant *numerical* quantity (the squared
norm, equivalently the Born weight of the transported one-dimensional
cell), not a persistence of the record-selection structure itself.

Pairwise-orthogonality preservation is derived from the complex
polarization identity in terms of norms
(`inner_eq_sum_norm_sq_div_four`), not assumed: a norm-preserving
`ℂ`-linear map preserves every inner product, since the polarization
identity expresses `⟪x, y⟫` purely from norms of linear combinations of
`x`, `y`, each of which the map leaves invariant.
-/

namespace QuantumFoundations.BranchesRiedel.BornBridge

open scoped InnerProductSpace Classical
open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.SimulatedEvolution

noncomputable section

variable {n : ℕ} {F : Type*} [Fintype F]

/-! ## C14k.0 — Norm-preserving maps preserve inner products -/

/-- **A norm-preserving `ℂ`-linear map preserves every inner product.**
Derived from the norm-based polarization identity, applied to `T x`/`T y`
and to `x`/`y`: since `T` is linear, `T x ± T y = T (x ± y)` and
`T x ± I • T y = T (x ± I • y)`, so every norm appearing in the polarization
formula for `⟪T x, T y⟫` reduces, via `IsNormPreserving`, to the
corresponding norm for `⟪x, y⟫`. -/
theorem IsNormPreserving.inner_map_map {T : H n →L[ℂ] H n} (hT : IsNormPreserving T)
    (x y : H n) : ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ := by
  have h1 : T (x + y) = T x + T y := map_add T x y
  have h2 : T (x - y) = T x - T y := map_sub T x y
  have h3 : T (x - (RCLike.I : ℂ) • y) = T x - (RCLike.I : ℂ) • T y := by
    rw [map_sub, map_smul]
  have h4 : T (x + (RCLike.I : ℂ) • y) = T x + (RCLike.I : ℂ) • T y := by
    rw [map_add, map_smul]
  rw [inner_eq_sum_norm_sq_div_four (T x) (T y), ← h1, ← h2, ← h3, ← h4, hT (x + y),
    hT (x - y), hT (x - (RCLike.I : ℂ) • y), hT (x + (RCLike.I : ℂ) • y),
    ← inner_eq_sum_norm_sq_div_four x y]

/-! ## C14k.1 — Evolved branches -/

/-- Every evolved active branch vector retains its original squared norm:
an immediate consequence of norm preservation. -/
theorem evolved_branch_norm_sq (U : NormPreservingEvolution (H n)) (t : ℝ) (B : F → H n)
    (f : ActiveBranchIndex B) :
    ‖U.evolve t (activeBranchVector B f)‖ ^ 2 = ‖activeBranchVector B f‖ ^ 2 := by
  rw [U.norm_apply]

/-- The evolved state decomposes as the sum of the evolved branches: from
reconstruction of `ψ` and linearity of `U.evolve t`. -/
theorem evolve_sum_branches (U : NormPreservingEvolution (H n)) (t : ℝ) (B : F → H n) {ψ : H n}
    (hsum : ∑ g : F, B g = ψ) : U.evolve t ψ = ∑ g : F, U.evolve t (B g) := by
  rw [← hsum, map_sum]

/-- Pairwise orthogonality is preserved by the (norm-preserving) evolution. -/
theorem evolved_branches_pairwise_orthogonal (U : NormPreservingEvolution (H n)) (t : ℝ)
    (B : F → H n) (hortho : Pairwise (fun x y : F => ⟪B x, B y⟫_ℂ = 0)) :
    Pairwise (fun x y : F => ⟪U.evolve t (B x), U.evolve t (B y)⟫_ℂ = 0) := by
  intro x y hxy
  rw [IsNormPreserving.inner_map_map (U.isNormPreserving t) (B x) (B y)]
  exact hortho hxy

/-! ## C14k.1 — Weight conservation -/

/-- **Weight conservation under evolution.** The state's projection onto
the transported one-dimensional cell `span {U.evolve t (B f)}` has the same
squared norm as the original branch vector — the invariant numerical
quantity. The evolved branch is *not* claimed to be selected by the
original record projectors; only this squared-norm identity is asserted. -/
theorem evolved_branch_Born_quantity_eq_initial (U : NormPreservingEvolution (H n)) (t : ℝ)
    (B : F → H n) {ψ : H n} (hsum : ∑ g : F, B g = ψ)
    (hortho : Pairwise (fun x y : F => ⟪B x, B y⟫_ℂ = 0)) (f : ActiveBranchIndex B) :
    ‖(Submodule.span ℂ {U.evolve t (activeBranchVector B f)}).starProjection (U.evolve t ψ)‖ ^ 2
      = ‖activeBranchVector B f‖ ^ 2 := by
  set B' : F → H n := fun g => U.evolve t (B g) with hB'_def
  have hsum' : ∑ g : F, B' g = U.evolve t ψ := (evolve_sum_branches U t B hsum).symm
  have hortho' : Pairwise (fun x y : F => ⟪B' x, B' y⟫_ℂ = 0) :=
    evolved_branches_pairwise_orthogonal U t B hortho
  have hf'ne : B' f.1 ≠ 0 := by
    show U.evolve t (B f.1) ≠ 0
    intro h
    apply activeBranchVector_ne_zero B f
    have hnorm : ‖U.evolve t (B f.1)‖ = 0 := by rw [h]; exact norm_zero
    rw [U.norm_apply] at hnorm
    exact norm_eq_zero.mp hnorm
  have hkey := bornQuantity_branchCell B' hsum' hortho' ⟨f.1, hf'ne⟩
  have hnormeq : ‖activeBranchVector B' ⟨f.1, hf'ne⟩‖ = ‖activeBranchVector B f‖ := by
    show ‖U.evolve t (B f.1)‖ = ‖activeBranchVector B f‖
    rw [U.norm_apply]; rfl
  rw [hnormeq] at hkey
  exact hkey

/-! ## C14k.2 — Connection to C13 persistence -/

/-- **Two simultaneous, logically distinct conclusions**: under the exact
C13 margin/simulation hypotheses, every evolved branch retains its squared
norm (a `C14` weight-conservation fact), *and* the normalized evolved
branch pair retains its proxy-complexity gap (`C13`'s
`margin_gap_persists_under_simulated_evolution`, unchanged). Neither
conclusion is derived from the other. -/
theorem evolved_branch_weight_and_gap_persist {N d : ℕ}
    (U : NormPreservingEvolution (H (d ^ N))) (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (a b : H (d ^ N)) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (δ μ ε : ℝ) (g : ℕ) (t : ℝ) (E : Circuit N d)
    (hGap : HasProxyGapMarginAtLeast e a b δ μ (4 * Circuit.length E + g))
    (hSim : CircuitSimulatesEvolutionAt U e t E ε) (hErr : 2 * ε ≤ μ) :
    (‖U.evolve t a‖ ^ 2 = ‖a‖ ^ 2 ∧ ‖U.evolve t b‖ ^ 2 = ‖b‖ ^ 2)
      ∧ HasProxyGapAtLeast e (U.evolve t a) (U.evolve t b) δ g :=
  ⟨⟨by rw [U.norm_apply], by rw [U.norm_apply]⟩,
    margin_gap_persists_under_simulated_evolution U e a b ha hb δ μ ε g t E hGap hSim hErr⟩

end

end QuantumFoundations.BranchesRiedel.BornBridge
