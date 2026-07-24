import Gleason.Busch.Main

/-!
# QB1 — Effect wrapper and basic operations

An **effect** (Busch 2003) is a complex-linear operator `T` satisfying `0 ≤ T
≤ 1` in the Loewner order — reusing exactly the pinned dependency's
`Gleason.IsEffect`, not a new competing notion of positivity. This file
defines the subtype wrapper `Effect n`, the zero/unit/projection effects,
and the effect complement, all directly from `Gleason.IsEffect` and
`Gleason.projL`.
-/

namespace QuantumFoundations.BornRule.EffectPerspectives

noncomputable section

/-- An effect on `Gleason.H n`: a complex-linear operator `T` with
`0 ≤ T ≤ 1` in the Loewner order, in the exact sense of `Gleason.IsEffect`. -/
abbrev Effect (n : ℕ) :=
  {T : Gleason.H n →ₗ[ℂ] Gleason.H n // Gleason.IsEffect T}

/-! ## QB1.1 — Zero and unit effects -/

/-- The zero effect: the orthogonal projection onto `⊥`. -/
def zeroEffect (n : ℕ) : Effect n :=
  ⟨Gleason.projL ⊥, Gleason.EffectMeasure.isEffect_projL ⊥⟩

/-- The unit effect: the orthogonal projection onto `⊤`. -/
def oneEffect (n : ℕ) : Effect n :=
  ⟨Gleason.projL ⊤, Gleason.EffectMeasure.isEffect_projL ⊤⟩

@[simp] theorem zeroEffect_coe (n : ℕ) :
    (zeroEffect n : Gleason.H n →ₗ[ℂ] Gleason.H n) = 0 := by
  show Gleason.projL ⊥ = 0
  simp [Gleason.projL, Submodule.starProjection_bot]

@[simp] theorem oneEffect_coe (n : ℕ) :
    (oneEffect n : Gleason.H n →ₗ[ℂ] Gleason.H n) = 1 := by
  show Gleason.projL ⊤ = 1
  simp [Gleason.projL, Submodule.starProjection_top']

/-! ## QB1.2 — Complement -/

/-- The complement of an effect: `1 - T`, itself an effect since
`Gleason.IsEffect` is exactly `IsPositiveOp T ∧ IsPositiveOp (1 - T)`. -/
def complementEffect {n : ℕ} (T : Effect n) : Effect n :=
  ⟨1 - T.1, by
    refine ⟨T.2.2, ?_⟩
    have heq : (1 : Gleason.H n →ₗ[ℂ] Gleason.H n) - (1 - T.1) = T.1 := by abel
    rw [heq]
    exact T.2.1⟩

@[simp] theorem complementEffect_coe {n : ℕ} (T : Effect n) :
    (complementEffect T : Gleason.H n →ₗ[ℂ] Gleason.H n) = 1 - T.1 := rfl

@[simp] theorem complementEffect_complement {n : ℕ} (T : Effect n) :
    complementEffect (complementEffect T) = T := by
  apply Subtype.ext
  show 1 - (1 - T.1) = T.1
  abel

@[simp] theorem complementEffect_zero (n : ℕ) :
    complementEffect (zeroEffect n) = oneEffect n := by
  apply Subtype.ext
  show 1 - (zeroEffect n : Gleason.H n →ₗ[ℂ] Gleason.H n) = (oneEffect n : Gleason.H n →ₗ[ℂ] Gleason.H n)
  simp

@[simp] theorem complementEffect_one (n : ℕ) :
    complementEffect (oneEffect n) = zeroEffect n := by
  apply Subtype.ext
  show 1 - (oneEffect n : Gleason.H n →ₗ[ℂ] Gleason.H n) = (zeroEffect n : Gleason.H n →ₗ[ℂ] Gleason.H n)
  simp

/-! ## QB1.3 — Projection effect -/

/-- The effect corresponding to an orthogonal projection onto a closed
subspace: reuses `Gleason.projL` directly, no new orthogonal projector is
defined. -/
def projectionEffect {n : ℕ} (A : Submodule ℂ (Gleason.H n)) : Effect n :=
  ⟨Gleason.projL A, Gleason.EffectMeasure.isEffect_projL A⟩

@[simp] theorem projectionEffect_coe {n : ℕ} (A : Submodule ℂ (Gleason.H n)) :
    (projectionEffect A : Gleason.H n →ₗ[ℂ] Gleason.H n) = Gleason.projL A := rfl

end

end QuantumFoundations.BornRule.EffectPerspectives
