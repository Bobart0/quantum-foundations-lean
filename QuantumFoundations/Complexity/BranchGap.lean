import QuantumFoundations.Complexity.RecordInterferenceBound
import QuantumFoundations.Complexity.RecordDistinguishability

/-!
# C6 — Exact redundant-record proxy-gap certificates

This file combines the physical lower and upper bounds before introducing
any order-theoretic minimum.  The gap is stated without subtraction.
-/

namespace QuantumFoundations.Complexity

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

/-- Exact redundant records provide an interference lower bound
`ceilHalf R`; an explicit record-readout circuit provides a
distinguishability upper bound `D.length`; therefore the proxy gap is at
least any `g` satisfying `D.length + g ≤ ceilHalf R`.

This is an exact finite-dimensional certificate.  It is not a persistence,
canonical-branching, or full Taylor–McCulloch theorem. -/
theorem redundant_records_give_proxy_gap_certificate
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (regions : Fin R → Finset (Fin N))
    (recs : Fin R → LabeledResolution (d ^ N) K) (ψ : H (d ^ N))
    (hrec : IsRecordedOn ψ recs) (r₀ : Fin R) (i j : Fin K) (hij : i ≠ j)
    (hi : branch recs ψ i ≠ 0) (hj : branch recs ψ j ≠ 0)
    (hlocal_i : ∀ r, IsLocalTo (transportedRecordProj e (recs r) i) (regions r))
    (hlocal_j : ∀ r, IsLocalTo (transportedRecordProj e (recs r) j) (regions r))
    (hpairwise : ∀ r r', r ≠ r' → Disjoint (regions r) (regions r'))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (D : Circuit N d) (hD : ImplementsRecordPhaseFlip e D (recs r₀) j)
    (g : ℕ) (hgap : Circuit.length D + g ≤ ceilHalf R) :
    HasProxyGapAtLeast e
      (normalizedBranch recs ψ i) (normalizedBranch recs ψ j) δ g := by
  refine ⟨ceilHalf R, Circuit.length D, ?_, ?_, hgap⟩
  · exact redundant_records_give_interference_lower_bound
      e regions recs ψ hrec i j hij hi hj hlocal_i hlocal_j hpairwise δ hδ0
  · exact record_phase_flip_gives_distinguishability_upper_bound
      e recs ψ hrec r₀ i j hij hi hj δ hδ0.le hδ1 D hD

#print axioms redundant_records_give_proxy_gap_certificate

end

end QuantumFoundations.Complexity
