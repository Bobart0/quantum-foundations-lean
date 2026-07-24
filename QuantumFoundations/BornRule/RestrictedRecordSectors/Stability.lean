import QuantumFoundations.BornRule.RestrictedRecordSectors.Hilbert

/-!
# C17 — Quantitative stability of restricted record-sector weights

The analytic core controls the change of a squared norm by the distance
between the underlying vectors.  The Hilbert-facing results apply this to
projected record-sector components whose exact quadratic weights are supplied
by C15.
-/

namespace QuantumFoundations.BornRule.RestrictedRecordSectors

open scoped NNReal InnerProductSpace BigOperators

/-! ## Generic norm-square estimates -/

/-- The difference of squared norms is controlled by the vector distance. -/
theorem abs_norm_sq_sub_norm_sq_le
    {E : Type*} [NormedAddCommGroup E]
    (u v : E) :
    |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤
      (‖u‖ + ‖v‖) * ‖u - v‖ := by
  calc
    |‖u‖ ^ 2 - ‖v‖ ^ 2| =
        |(‖u‖ - ‖v‖) * (‖u‖ + ‖v‖)| := by
          congr 1
          ring
    _ = |‖u‖ - ‖v‖| * |‖u‖ + ‖v‖| := abs_mul _ _
    _ = |‖u‖ - ‖v‖| * (‖u‖ + ‖v‖) := by
      rw [abs_of_nonneg (add_nonneg (norm_nonneg u) (norm_nonneg v))]
    _ ≤ ‖u - v‖ * (‖u‖ + ‖v‖) :=
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le u v)
        (add_nonneg (norm_nonneg u) (norm_nonneg v))
    _ = (‖u‖ + ‖v‖) * ‖u - v‖ := mul_comm _ _

/-- On the unit ball, the preceding estimate has the uniform constant two. -/
theorem abs_norm_sq_sub_norm_sq_le_two_mul
    {E : Type*} [NormedAddCommGroup E]
    (u v : E)
    (hu : ‖u‖ ≤ 1)
    (hv : ‖v‖ ≤ 1) :
    |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ 2 * ‖u - v‖ := by
  calc
    |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤
        (‖u‖ + ‖v‖) * ‖u - v‖ :=
      abs_norm_sq_sub_norm_sq_le u v
    _ ≤ 2 * ‖u - v‖ := by
      apply mul_le_mul_of_nonneg_right
      · linarith
      · exact norm_nonneg _

/-! ## Projected components and exact quadratic weights -/

variable {σ : Type*} {n : ℕ}

noncomputable section

/-- The projected component of an admissible Hilbert record situation. -/
def projectedComponent
    (L : HilbertRecordLayer σ n)
    (x : σ) : Gleason.H n :=
  (L.sector x).starProjection (L.state x)

@[simp]
theorem projectedComponent_apply
    (L : HilbertRecordLayer σ n) (x : σ) :
    projectedComponent L x =
      (L.sector x).starProjection (L.state x) :=
  rfl

/-- Interface asserting that a weight already obeys the exact normalized
quadratic law supplied by C15. -/
def QuadraticWeightLaw
    (L : HilbertRecordLayer σ n)
    (W : σ → ℝ≥0) : Prop :=
  ∀ x : σ, W x = ‖projectedComponent L x‖₊ ^ 2

/-- The normalized C15 theorem supplies the quadratic-weight interface used
by C17. -/
theorem quadraticWeightLaw_of_restricted_record_sector_born
    (L : HilbertRecordLayer σ n)
    (W : σ → ℝ≥0)
    (hrealized : AllMagnitudesRealized L.toBinaryRefinementSystem)
    (hsaturated : BinarySaturated L.toBinaryRefinementSystem)
    (hstable : RefinementStable L.toBinaryRefinementSystem W)
    (hequiv : InternalEquivalence L.toBinaryRefinementSystem W)
    (family : Finset σ)
    (hWeightNorm : ∑ x ∈ family, W x = 1)
    (hMagnitudeNorm :
      ∑ x ∈ family,
        ‖(L.sector x).starProjection (L.state x)‖₊ ^ 2 = 1) :
    QuadraticWeightLaw L W := by
  intro x
  simpa only [projectedComponent] using
    restricted_record_sector_born L W hrealized hsaturated hstable hequiv
      family hWeightNorm hMagnitudeNorm x

/-! ## Pointwise stability -/

/-- Exact quadratic weights inherit the generic norm-square stability bound
for their projected components. -/
theorem quadraticWeightLaw_pointwise_stability
    {L₁ L₂ : HilbertRecordLayer σ n}
    {W₁ W₂ : σ → ℝ≥0}
    (h₁ : QuadraticWeightLaw L₁ W₁)
    (h₂ : QuadraticWeightLaw L₂ W₂)
    (x : σ) :
    |(W₁ x : ℝ) - (W₂ x : ℝ)| ≤
      (‖projectedComponent L₁ x‖ + ‖projectedComponent L₂ x‖) *
        ‖projectedComponent L₁ x - projectedComponent L₂ x‖ := by
  have h₁real := congrArg NNReal.toReal (h₁ x)
  have h₂real := congrArg NNReal.toReal (h₂ x)
  simp only [NNReal.coe_pow, coe_nnnorm] at h₁real h₂real
  rw [h₁real, h₂real]
  exact abs_norm_sq_sub_norm_sq_le
    (projectedComponent L₁ x) (projectedComponent L₂ x)

/-- Pointwise stability with constant two when both projected components lie
in the unit ball. -/
theorem quadraticWeightLaw_pointwise_stability_of_unit_bound
    {L₁ L₂ : HilbertRecordLayer σ n}
    {W₁ W₂ : σ → ℝ≥0}
    (h₁ : QuadraticWeightLaw L₁ W₁)
    (h₂ : QuadraticWeightLaw L₂ W₂)
    (x : σ)
    (hu : ‖projectedComponent L₁ x‖ ≤ 1)
    (hv : ‖projectedComponent L₂ x‖ ≤ 1) :
    |(W₁ x : ℝ) - (W₂ x : ℝ)| ≤
      2 * ‖projectedComponent L₁ x - projectedComponent L₂ x‖ := by
  have h₁real := congrArg NNReal.toReal (h₁ x)
  have h₂real := congrArg NNReal.toReal (h₂ x)
  simp only [NNReal.coe_pow, coe_nnnorm] at h₁real h₂real
  rw [h₁real, h₂real]
  exact abs_norm_sq_sub_norm_sq_le_two_mul
    (projectedComponent L₁ x) (projectedComponent L₂ x) hu hv

/-! ## Finite-family stability -/

/-- Sum the pointwise stability estimate over a finite family. -/
theorem quadraticWeightLaw_l1_stability
    {L₁ L₂ : HilbertRecordLayer σ n}
    {W₁ W₂ : σ → ℝ≥0}
    (h₁ : QuadraticWeightLaw L₁ W₁)
    (h₂ : QuadraticWeightLaw L₂ W₂)
    (s : Finset σ) :
    ∑ x ∈ s, |(W₁ x : ℝ) - (W₂ x : ℝ)| ≤
      ∑ x ∈ s,
        (‖projectedComponent L₁ x‖ + ‖projectedComponent L₂ x‖) *
          ‖projectedComponent L₁ x - projectedComponent L₂ x‖ := by
  apply Finset.sum_le_sum
  intro x hx
  exact quadraticWeightLaw_pointwise_stability h₁ h₂ x

/-- On the unit ball, the finite-family `L¹` discrepancy is at most twice
the sum of projected-component distances. -/
theorem quadraticWeightLaw_l1_stability_of_unit_bound
    {L₁ L₂ : HilbertRecordLayer σ n}
    {W₁ W₂ : σ → ℝ≥0}
    (h₁ : QuadraticWeightLaw L₁ W₁)
    (h₂ : QuadraticWeightLaw L₂ W₂)
    (s : Finset σ)
    (hu : ∀ x ∈ s, ‖projectedComponent L₁ x‖ ≤ 1)
    (hv : ∀ x ∈ s, ‖projectedComponent L₂ x‖ ≤ 1) :
    ∑ x ∈ s, |(W₁ x : ℝ) - (W₂ x : ℝ)| ≤
      2 * ∑ x ∈ s,
        ‖projectedComponent L₁ x - projectedComponent L₂ x‖ := by
  calc
    (∑ x ∈ s, |(W₁ x : ℝ) - (W₂ x : ℝ)|) ≤
        ∑ x ∈ s,
          2 * ‖projectedComponent L₁ x - projectedComponent L₂ x‖ := by
      apply Finset.sum_le_sum
      intro x hx
      exact quadraticWeightLaw_pointwise_stability_of_unit_bound
        h₁ h₂ x (hu x hx) (hv x hx)
    _ = 2 * ∑ x ∈ s,
        ‖projectedComponent L₁ x - projectedComponent L₂ x‖ := by
      rw [Finset.mul_sum]

/-! ## Uniform-error and half-`L¹` corollaries -/

/-- A uniform component error `ε` gives the explicit finite-family bound
`2 * card(s) * ε`. -/
theorem quadraticWeightLaw_l1_stability_of_uniform_error
    {L₁ L₂ : HilbertRecordLayer σ n}
    {W₁ W₂ : σ → ℝ≥0}
    (h₁ : QuadraticWeightLaw L₁ W₁)
    (h₂ : QuadraticWeightLaw L₂ W₂)
    (s : Finset σ)
    (ε : ℝ)
    (_hε : 0 ≤ ε)
    (hu : ∀ x ∈ s, ‖projectedComponent L₁ x‖ ≤ 1)
    (hv : ∀ x ∈ s, ‖projectedComponent L₂ x‖ ≤ 1)
    (hdist : ∀ x ∈ s,
      ‖projectedComponent L₁ x - projectedComponent L₂ x‖ ≤ ε) :
    ∑ x ∈ s, |(W₁ x : ℝ) - (W₂ x : ℝ)| ≤
      2 * (s.card : ℝ) * ε := by
  have hsum :
      (∑ x ∈ s,
        ‖projectedComponent L₁ x - projectedComponent L₂ x‖) ≤
          (s.card : ℝ) * ε := by
    calc
      (∑ x ∈ s,
          ‖projectedComponent L₁ x - projectedComponent L₂ x‖) ≤
          ∑ x ∈ s, ε := by
        apply Finset.sum_le_sum
        intro x hx
        exact hdist x hx
      _ = (s.card : ℝ) * ε := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  calc
    (∑ x ∈ s, |(W₁ x : ℝ) - (W₂ x : ℝ)|) ≤
        2 * ∑ x ∈ s,
          ‖projectedComponent L₁ x - projectedComponent L₂ x‖ :=
      quadraticWeightLaw_l1_stability_of_unit_bound h₁ h₂ s hu hv
    _ ≤ 2 * ((s.card : ℝ) * ε) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 2 * (s.card : ℝ) * ε := by ring

/-- The corresponding half-`L¹` finite-family bound. -/
theorem quadraticWeightLaw_half_l1_stability_of_uniform_error
    {L₁ L₂ : HilbertRecordLayer σ n}
    {W₁ W₂ : σ → ℝ≥0}
    (h₁ : QuadraticWeightLaw L₁ W₁)
    (h₂ : QuadraticWeightLaw L₂ W₂)
    (s : Finset σ)
    (ε : ℝ)
    (hε : 0 ≤ ε)
    (hu : ∀ x ∈ s, ‖projectedComponent L₁ x‖ ≤ 1)
    (hv : ∀ x ∈ s, ‖projectedComponent L₂ x‖ ≤ 1)
    (hdist : ∀ x ∈ s,
      ‖projectedComponent L₁ x - projectedComponent L₂ x‖ ≤ ε) :
    (1 / 2 : ℝ) *
        ∑ x ∈ s, |(W₁ x : ℝ) - (W₂ x : ℝ)| ≤
      (s.card : ℝ) * ε := by
  have hbound :=
    quadraticWeightLaw_l1_stability_of_uniform_error
      h₁ h₂ s ε hε hu hv hdist
  calc
    (1 / 2 : ℝ) *
        ∑ x ∈ s, |(W₁ x : ℝ) - (W₂ x : ℝ)| ≤
        (1 / 2 : ℝ) * (2 * (s.card : ℝ) * ε) :=
      mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = (s.card : ℝ) * ε := by ring

/-! ## State-norm adapters -/

/-- Orthogonal projection does not increase the norm. -/
theorem projectedComponent_norm_le_state_norm
    (L : HilbertRecordLayer σ n)
    (x : σ) :
    ‖projectedComponent L x‖ ≤ ‖L.state x‖ := by
  exact (L.sector x).norm_starProjection_apply_le (L.state x)

/-- Component unit-ball bounds follow from state unit-ball bounds. -/
theorem quadraticWeightLaw_pointwise_stability_of_state_bound
    {L₁ L₂ : HilbertRecordLayer σ n}
    {W₁ W₂ : σ → ℝ≥0}
    (h₁ : QuadraticWeightLaw L₁ W₁)
    (h₂ : QuadraticWeightLaw L₂ W₂)
    (x : σ)
    (hstate₁ : ‖L₁.state x‖ ≤ 1)
    (hstate₂ : ‖L₂.state x‖ ≤ 1) :
    |(W₁ x : ℝ) - (W₂ x : ℝ)| ≤
      2 * ‖projectedComponent L₁ x - projectedComponent L₂ x‖ := by
  apply quadraticWeightLaw_pointwise_stability_of_unit_bound h₁ h₂ x
  · exact (projectedComponent_norm_le_state_norm L₁ x).trans hstate₁
  · exact (projectedComponent_norm_le_state_norm L₂ x).trans hstate₂

/-- In particular, normalized states give the pointwise constant-two bound. -/
theorem quadraticWeightLaw_pointwise_stability_of_normalized_states
    {L₁ L₂ : HilbertRecordLayer σ n}
    {W₁ W₂ : σ → ℝ≥0}
    (h₁ : QuadraticWeightLaw L₁ W₁)
    (h₂ : QuadraticWeightLaw L₂ W₂)
    (x : σ)
    (hstate₁ : ‖L₁.state x‖ = 1)
    (hstate₂ : ‖L₂.state x‖ = 1) :
    |(W₁ x : ℝ) - (W₂ x : ℝ)| ≤
      2 * ‖projectedComponent L₁ x - projectedComponent L₂ x‖ :=
  quadraticWeightLaw_pointwise_stability_of_state_bound
    h₁ h₂ x hstate₁.le hstate₂.le

/-! ## Paper-facing C17 names -/

/-- Paper-facing pointwise stability theorem. -/
theorem restricted_record_sector_weight_pointwise_stability
    {L₁ L₂ : HilbertRecordLayer σ n}
    {W₁ W₂ : σ → ℝ≥0}
    (h₁ : QuadraticWeightLaw L₁ W₁)
    (h₂ : QuadraticWeightLaw L₂ W₂)
    (x : σ) :
    |(W₁ x : ℝ) - (W₂ x : ℝ)| ≤
      (‖projectedComponent L₁ x‖ + ‖projectedComponent L₂ x‖) *
        ‖projectedComponent L₁ x - projectedComponent L₂ x‖ :=
  quadraticWeightLaw_pointwise_stability h₁ h₂ x

/-- Paper-facing finite-family stability theorem. -/
theorem restricted_record_sector_weight_l1_stability
    {L₁ L₂ : HilbertRecordLayer σ n}
    {W₁ W₂ : σ → ℝ≥0}
    (h₁ : QuadraticWeightLaw L₁ W₁)
    (h₂ : QuadraticWeightLaw L₂ W₂)
    (s : Finset σ)
    (hu : ∀ x ∈ s, ‖projectedComponent L₁ x‖ ≤ 1)
    (hv : ∀ x ∈ s, ‖projectedComponent L₂ x‖ ≤ 1) :
    ∑ x ∈ s, |(W₁ x : ℝ) - (W₂ x : ℝ)| ≤
      2 * ∑ x ∈ s,
        ‖projectedComponent L₁ x - projectedComponent L₂ x‖ :=
  quadraticWeightLaw_l1_stability_of_unit_bound h₁ h₂ s hu hv

/-- Paper-facing uniform-error stability theorem. -/
theorem restricted_record_sector_weight_uniform_stability
    {L₁ L₂ : HilbertRecordLayer σ n}
    {W₁ W₂ : σ → ℝ≥0}
    (h₁ : QuadraticWeightLaw L₁ W₁)
    (h₂ : QuadraticWeightLaw L₂ W₂)
    (s : Finset σ)
    (ε : ℝ)
    (hε : 0 ≤ ε)
    (hu : ∀ x ∈ s, ‖projectedComponent L₁ x‖ ≤ 1)
    (hv : ∀ x ∈ s, ‖projectedComponent L₂ x‖ ≤ 1)
    (hdist : ∀ x ∈ s,
      ‖projectedComponent L₁ x - projectedComponent L₂ x‖ ≤ ε) :
    ∑ x ∈ s, |(W₁ x : ℝ) - (W₂ x : ℝ)| ≤
      2 * (s.card : ℝ) * ε :=
  quadraticWeightLaw_l1_stability_of_uniform_error
    h₁ h₂ s ε hε hu hv hdist

end

end QuantumFoundations.BornRule.RestrictedRecordSectors
