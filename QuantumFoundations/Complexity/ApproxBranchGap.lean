import QuantumFoundations.Complexity.ApproxRecordDistinguishability

/-!
# C8e — Robust proxy-gap certificates from approximate records

The interference and distinguishability estimates are combined first as a
finite relational certificate.  The `WithTop ℕ` theorem is then a direct
reuse of the existing certificate-to-minimum API.
-/

namespace QuantumFoundations.Complexity

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

/-- Approximate redundant records and a supplied approximate phase-readout
circuit certify a subtraction-free proxy gap. -/
theorem approximate_records_give_proxy_gap_certificate
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (regions : Fin R → Finset (Fin N))
    (recs : Fin R → LabeledResolution (d ^ N) K)
    (a b : H (d ^ N)) (r₀ : Fin R) (i j : Fin K)
    (ηi ηj ξ δ : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (happrox : ApproxRecordedPairOn recs a b i j ηi ηj)
    (hlocal_i : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) i) (regions r))
    (hlocal_j : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) j) (regions r))
    (hpairwise : ∀ r r', r ≠ r' → Disjoint (regions r) (regions r'))
    (hInterferenceThreshold : ηi + ηj < 2 * δ)
    (D : Circuit N d)
    (hRead : ApproximatesRecordPhaseFlipOn e D (recs r₀) j a b ξ)
    (hDistinguishabilityThreshold : 2 * δ + 2 * ηj + ξ ≤ 2)
    (g : ℕ) (hgap : Circuit.length D + g ≤ ceilHalf R) :
    HasProxyGapAtLeast e a b δ g := by
  refine ⟨ceilHalf R, Circuit.length D, ?_, ?_, hgap⟩
  · exact approximate_records_give_interference_lower_bound
      e regions recs a b i j ηi ηj δ ha hb happrox hlocal_i hlocal_j
      hpairwise hInterferenceThreshold
  · exact approx_record_phase_flip_gives_upper_bound
      e D (recs r₀) j a b ηj ξ δ ha hb (happrox r₀).2 hRead
      hDistinguishabilityThreshold

/-- The same robust gap holds for the actual exact circuit minima in
`WithTop ℕ`. -/
theorem approximate_records_complexity_gap
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (regions : Fin R → Finset (Fin N))
    (recs : Fin R → LabeledResolution (d ^ N) K)
    (a b : H (d ^ N)) (r₀ : Fin R) (i j : Fin K)
    (ηi ηj ξ δ : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (happrox : ApproxRecordedPairOn recs a b i j ηi ηj)
    (hlocal_i : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) i) (regions r))
    (hlocal_j : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) j) (regions r))
    (hpairwise : ∀ r r', r ≠ r' → Disjoint (regions r) (regions r'))
    (hInterferenceThreshold : ηi + ηj < 2 * δ)
    (D : Circuit N d)
    (hRead : ApproximatesRecordPhaseFlipOn e D (recs r₀) j a b ξ)
    (hDistinguishabilityThreshold : 2 * δ + 2 * ηj + ξ ≤ 2)
    (g : ℕ) (hgap : Circuit.length D + g ≤ ceilHalf R) :
    distinguishabilityComplexity e a b δ + (g : WithTop ℕ) ≤
      interferenceComplexity e a b δ := by
  have hI := approximate_records_give_interference_lower_bound
    e regions recs a b i j ηi ηj δ ha hb happrox hlocal_i hlocal_j
    hpairwise hInterferenceThreshold
  have hD := approx_record_phase_flip_gives_upper_bound
    e D (recs r₀) j a b ηj ξ δ ha hb (happrox r₀).2 hRead
    hDistinguishabilityThreshold
  have hImin := interferenceLowerBound_le_complexity hI
  have hDmin := complexity_le_of_distinguishabilityUpperBound hD
  calc
    distinguishabilityComplexity e a b δ + (g : WithTop ℕ)
        ≤ (Circuit.length D : WithTop ℕ) + (g : WithTop ℕ) :=
      add_le_add hDmin le_rfl
    _ = (Circuit.length D + g : ℕ) := by norm_num
    _ ≤ (ceilHalf R : WithTop ℕ) := by exact_mod_cast hgap
    _ ≤ interferenceComplexity e a b δ := hImin

/-- Branch-specific specialization with an explicit approximate-record
assumption.  No exact `IsRecordedOn` hypothesis is used. -/
theorem approximate_normalized_branches_give_proxy_gap_certificate
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (regions : Fin R → Finset (Fin N))
    (recs : Fin R → LabeledResolution (d ^ N) K) (ψ : H (d ^ N))
    (r₀ : Fin R) (i j : Fin K)
    (hi : branch recs ψ i ≠ 0) (hj : branch recs ψ j ≠ 0)
    (ηi ηj ξ δ : ℝ)
    (happrox : ApproxRecordedPairOn recs
      (normalizedBranch recs ψ i) (normalizedBranch recs ψ j) i j ηi ηj)
    (hlocal_i : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) i) (regions r))
    (hlocal_j : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) j) (regions r))
    (hpairwise : ∀ r r', r ≠ r' → Disjoint (regions r) (regions r'))
    (hInterferenceThreshold : ηi + ηj < 2 * δ)
    (D : Circuit N d)
    (hRead : ApproximatesRecordPhaseFlipOn e D (recs r₀) j
      (normalizedBranch recs ψ i) (normalizedBranch recs ψ j) ξ)
    (hDistinguishabilityThreshold : 2 * δ + 2 * ηj + ξ ≤ 2)
    (g : ℕ) (hgap : Circuit.length D + g ≤ ceilHalf R) :
    HasProxyGapAtLeast e
      (normalizedBranch recs ψ i) (normalizedBranch recs ψ j) δ g := by
  exact approximate_records_give_proxy_gap_certificate
    e regions recs (normalizedBranch recs ψ i) (normalizedBranch recs ψ j)
    r₀ i j ηi ηj ξ δ
    (normalizedBranch_norm recs ψ i hi) (normalizedBranch_norm recs ψ j hj)
    happrox hlocal_i hlocal_j hpairwise hInterferenceThreshold D hRead
    hDistinguishabilityThreshold g hgap

/-- Regression theorem: exact records and an exact phase flip instantiate the
robust certificate with all analytic errors equal to zero. -/
theorem exact_records_recover_approximate_proxy_gap_certificate
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (regions : Fin R → Finset (Fin N))
    (recs : Fin R → LabeledResolution (d ^ N) K) (ψ : H (d ^ N))
    (hrec : IsRecordedOn ψ recs) (r₀ : Fin R) (i j : Fin K) (hij : i ≠ j)
    (hi : branch recs ψ i ≠ 0) (hj : branch recs ψ j ≠ 0)
    (hlocal_i : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) i) (regions r))
    (hlocal_j : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) j) (regions r))
    (hpairwise : ∀ r r', r ≠ r' → Disjoint (regions r) (regions r'))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (D : Circuit N d) (hD : ImplementsRecordPhaseFlip e D (recs r₀) j)
    (g : ℕ) (hgap : Circuit.length D + g ≤ ceilHalf R) :
    HasProxyGapAtLeast e
      (normalizedBranch recs ψ i) (normalizedBranch recs ψ j) δ g := by
  exact approximate_normalized_branches_give_proxy_gap_certificate
    e regions recs ψ r₀ i j hi hj 0 0 0 δ
    (exact_records_give_approxRecordedPairOn_zero recs ψ hrec i j hij hi hj)
    hlocal_i hlocal_j hpairwise (by linarith) D
    (implementsRecordPhaseFlip_gives_approximation_zero
      e D (recs r₀) j (normalizedBranch recs ψ i) (normalizedBranch recs ψ j) hD)
    (by linarith) g hgap

#print axioms approximate_records_give_proxy_gap_certificate
#print axioms approximate_records_complexity_gap

end


end QuantumFoundations.Complexity
