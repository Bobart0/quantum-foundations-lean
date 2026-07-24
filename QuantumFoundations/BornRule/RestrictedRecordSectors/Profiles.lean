import QuantumFoundations.BornRule.RestrictedRecordSectors.Basic

/-!
# C15c–e — Binary profiles and the scalar functional equation

Internal equivalence is stated as invariance under equality of binary
refinement profiles.  Saturation, rather than the definition, proves that
these profiles are classified by magnitude.  The induced one-variable
function then satisfies a Pythagorean equation, whose squared reparameterized
form is additive.
-/

namespace QuantumFoundations.BornRule.RestrictedRecordSectors

open scoped NNReal Classical

noncomputable section

variable {σ : Type*}

/-- The trivial self-profile together with all realized binary refinements. -/
def BinaryProfile (S : BinaryRefinementSystem σ) (x : σ) : Set (ℝ≥0 × ℝ≥0) :=
  { pair |
    pair = (S.magnitude x, 0) ∨
      ∃ left right,
        S.refines x left right ∧
          pair = (S.magnitude left, S.magnitude right) }

/-- Weights are invariant under equality of internal binary profiles. -/
def InternalEquivalence
    (S : BinaryRefinementSystem σ) (W : σ → ℝ≥0) : Prop :=
  ∀ {x y}, BinaryProfile S x = BinaryProfile S y → W x = W y

/-- Under saturation, a binary profile is exactly the Pythagorean circle
with radius equal to the situation's magnitude. -/
theorem mem_binaryProfile_iff
    {S : BinaryRefinementSystem σ}
    (hsat : BinarySaturated S)
    {x : σ} {pair : ℝ≥0 × ℝ≥0} :
    pair ∈ BinaryProfile S x ↔
      pair.1 ^ 2 + pair.2 ^ 2 = S.magnitude x ^ 2 := by
  constructor
  · intro hpair
    rcases hpair with htrivial | ⟨left, right, href, hpair⟩
    · subst pair
      norm_num
    · subst pair
      exact (S.pythagorean href).symm
  · intro hsq
    obtain ⟨left, right, href, hleft, hright⟩ :=
      hsat x pair.1 pair.2 hsq
    exact Or.inr ⟨left, right, href, by rw [hleft, hright]⟩

/-- Saturation classifies binary profiles precisely by magnitude. -/
theorem binaryProfile_eq_iff_magnitude_eq
    {S : BinaryRefinementSystem σ}
    (hsat : BinarySaturated S)
    {x y : σ} :
    BinaryProfile S x = BinaryProfile S y ↔
      S.magnitude x = S.magnitude y := by
  constructor
  · intro hprofile
    have hmemx : (S.magnitude x, 0) ∈ BinaryProfile S x := Or.inl rfl
    have hmemy : (S.magnitude x, 0) ∈ BinaryProfile S y := by
      rw [← hprofile]
      exact hmemx
    have hsq := (mem_binaryProfile_iff hsat).mp hmemy
    norm_num at hsq
    exact hsq
  · intro hmag
    apply Set.ext
    intro pair
    rw [mem_binaryProfile_iff hsat, mem_binaryProfile_iff hsat, hmag]

/-- Profile invariance therefore implies equality of weights at equal
magnitudes, without assuming norm invariance in the definition. -/
theorem weight_eq_of_magnitude_eq
    {S : BinaryRefinementSystem σ}
    {W : σ → ℝ≥0}
    (hsat : BinarySaturated S)
    (hequiv : InternalEquivalence S W)
    {x y : σ}
    (hxy : S.magnitude x = S.magnitude y) :
    W x = W y :=
  hequiv ((binaryProfile_eq_iff_magnitude_eq hsat).2 hxy)

/-- A total profile function.  If a magnitude is not represented, its value
is set to zero; under `AllMagnitudesRealized`, only the represented branch is
used. -/
noncomputable def profileFunction
    (S : BinaryRefinementSystem σ) (W : σ → ℝ≥0) (r : ℝ≥0) : ℝ≥0 :=
  if h : ∃ x : σ, S.magnitude x = r then W (Classical.choose h) else 0

private theorem profileFunction_spec
    {S : BinaryRefinementSystem σ}
    {W : σ → ℝ≥0}
    (hrealized : AllMagnitudesRealized S)
    (hsat : BinarySaturated S)
    (hequiv : InternalEquivalence S W)
    (r : ℝ≥0) :
    ∃ x : σ, S.magnitude x = r ∧ profileFunction S W r = W x := by
  obtain ⟨x, hx⟩ := hrealized r
  have hex : ∃ y : σ, S.magnitude y = r := ⟨x, hx⟩
  refine ⟨x, hx, ?_⟩
  rw [profileFunction, dif_pos hex]
  exact weight_eq_of_magnitude_eq (S := S) (W := W) hsat hequiv
    ((Classical.choose_spec hex).trans hx.symm)

/-- Every weight is the scalar profile function evaluated at its magnitude. -/
theorem weight_eq_profileFunction
    {S : BinaryRefinementSystem σ}
    {W : σ → ℝ≥0}
    (hrealized : AllMagnitudesRealized S)
    (hsat : BinarySaturated S)
    (hequiv : InternalEquivalence S W)
    (x : σ) :
    W x = profileFunction S W (S.magnitude x) := by
  obtain ⟨y, hy, hprofile⟩ :=
    profileFunction_spec hrealized hsat hequiv (S.magnitude x)
  rw [hprofile]
  exact weight_eq_of_magnitude_eq hsat hequiv hy.symm

/-- The profile function obeys the Pythagorean functional equation. -/
theorem profileFunction_pythagorean
    {S : BinaryRefinementSystem σ}
    {W : σ → ℝ≥0}
    (hrealized : AllMagnitudesRealized S)
    (hsat : BinarySaturated S)
    (hstable : RefinementStable S W)
    (hequiv : InternalEquivalence S W)
    (r₁ r₂ : ℝ≥0) :
    profileFunction S W (NNReal.sqrt (r₁ ^ 2 + r₂ ^ 2)) =
      profileFunction S W r₁ + profileFunction S W r₂ := by
  obtain ⟨parent, hparent⟩ :=
    hrealized (NNReal.sqrt (r₁ ^ 2 + r₂ ^ 2))
  have hsplit :
      r₁ ^ 2 + r₂ ^ 2 = S.magnitude parent ^ 2 := by
    rw [hparent, NNReal.sq_sqrt]
  obtain ⟨left, right, href, hleft, hright⟩ :=
    hsat parent r₁ r₂ hsplit
  have hp := weight_eq_profileFunction hrealized hsat hequiv parent
  have hl := weight_eq_profileFunction hrealized hsat hequiv left
  have hr := weight_eq_profileFunction hrealized hsat hequiv right
  rw [hparent] at hp
  rw [hleft] at hl
  rw [hright] at hr
  calc
    profileFunction S W (NNReal.sqrt (r₁ ^ 2 + r₂ ^ 2)) = W parent := hp.symm
    _ = W left + W right := hstable href
    _ = profileFunction S W r₁ + profileFunction S W r₂ := by rw [hl, hr]

/-- Reparameterize the magnitude profile by squared magnitude. -/
noncomputable def squaredProfileFunction
    (S : BinaryRefinementSystem σ) (W : σ → ℝ≥0) (u : ℝ≥0) : ℝ≥0 :=
  profileFunction S W (NNReal.sqrt u)

/-- The squared profile function is additive. -/
theorem squaredProfileFunction_additive
    {S : BinaryRefinementSystem σ}
    {W : σ → ℝ≥0}
    (hrealized : AllMagnitudesRealized S)
    (hsat : BinarySaturated S)
    (hstable : RefinementStable S W)
    (hequiv : InternalEquivalence S W) :
    ∀ u v,
      squaredProfileFunction S W (u + v) =
        squaredProfileFunction S W u + squaredProfileFunction S W v := by
  intro u v
  simpa only [squaredProfileFunction, NNReal.sq_sqrt] using
    profileFunction_pythagorean hrealized hsat hstable hequiv
      (NNReal.sqrt u) (NNReal.sqrt v)

/-- The scalar profile is forced to be quadratic. -/
theorem exists_profileFunction_quadratic
    {S : BinaryRefinementSystem σ}
    {W : σ → ℝ≥0}
    (hrealized : AllMagnitudesRealized S)
    (hsat : BinarySaturated S)
    (hstable : RefinementStable S W)
    (hequiv : InternalEquivalence S W) :
    ∃ c : ℝ≥0, ∀ r : ℝ≥0, profileFunction S W r = c * r ^ 2 := by
  obtain ⟨c, hc⟩ :=
    nnreal_additive_eq_mul (squaredProfileFunction S W)
      (squaredProfileFunction_additive hrealized hsat hstable hequiv)
  refine ⟨c, fun r => ?_⟩
  have hcr := hc (r ^ 2)
  simpa only [squaredProfileFunction, NNReal.sqrt_sq] using hcr

end

end QuantumFoundations.BornRule.RestrictedRecordSectors
