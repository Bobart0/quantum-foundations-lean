import QuantumFoundations.Complexity.ApproxRecordInterferenceBound
import QuantumFoundations.Complexity.RecordDistinguishability

/-!
# C8d — Approximate record readout and distinguishability

The readout approximation is pointwise on the two states used by the proxy;
no operator-norm infrastructure or synthesis assumption is introduced.  The
diagonal gap loses exactly twice the target-label record error plus the
aggregate readout error.
-/

namespace QuantumFoundations.Complexity

open scoped InnerProductSpace

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

/-- A supplied circuit approximates the exact record phase flip on the two
states of interest with aggregate pointwise error at most `ξ`. -/
def ApproximatesRecordPhaseFlipOn {N d K : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (D : Circuit N d)
    (Λ : LabeledResolution (d ^ N) K) (j : Fin K)
    (a b : H (d ^ N)) (ξ : ℝ) : Prop :=
  ‖Circuit.evalOnH D e a - recordPhaseFlip Λ j a‖ +
    ‖Circuit.evalOnH D e b - recordPhaseFlip Λ j b‖ ≤ ξ

namespace ApproximatesRecordPhaseFlipOn

/-- Increasing the pointwise readout-error budget preserves approximation. -/
theorem mono {N d K : ℕ}
    {e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d} {D : Circuit N d}
    {Λ : LabeledResolution (d ^ N) K} {j : Fin K}
    {a b : H (d ^ N)} {ξ ξ' : ℝ}
    (h : ApproximatesRecordPhaseFlipOn e D Λ j a b ξ) (hξ : ξ ≤ ξ') :
    ApproximatesRecordPhaseFlipOn e D Λ j a b ξ' :=
  h.trans hξ

end ApproximatesRecordPhaseFlipOn

/-- Exact circuit implementation gives pointwise approximation error zero on
every pair of states. -/
theorem implementsRecordPhaseFlip_gives_approximation_zero
    {N d K : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (D : Circuit N d)
    (Λ : LabeledResolution (d ^ N) K) (j : Fin K)
    (a b : H (d ^ N)) (hD : ImplementsRecordPhaseFlip e D Λ j) :
    ApproximatesRecordPhaseFlipOn e D Λ j a b 0 := by
  unfold ApproximatesRecordPhaseFlipOn ImplementsRecordPhaseFlip at *
  rw [hD]
  simp

/-- The approximate phase-readout diagonal gap is at least
`2 - (2 * ηj + ξ)` for unit states. -/
theorem diagonal_gap_lower_bound_of_approx_phase_flip
    {N d K : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (D : Circuit N d)
    (Λ : LabeledResolution (d ^ N) K) (j : Fin K)
    (a b : H (d ^ N)) (ηj ξ : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hrecord : ApproxRecordFor (rproj Λ j) b a ηj)
    (hread : ApproximatesRecordPhaseFlipOn e D Λ j a b ξ) :
    2 - (2 * ηj + ξ) ≤
      ‖⟪a, Circuit.evalOnH D e a⟫_ℂ -
        ⟪b, Circuit.evalOnH D e b⟫_ℂ‖ := by
  let U := Circuit.evalOnH D e
  let P := rproj Λ j
  let Z := recordPhaseFlip Λ j
  have haa : ⟪a, a⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, ha]
    norm_num
  have hbb : ⟪b, b⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hb]
    norm_num
  have hZa : Z a + a = (2 : ℂ) • P a := by
    simp [Z, P, recordPhaseFlip]
  have hZb : Z b - b = (2 : ℂ) • (P b - b) := by
    simp [Z, P, recordPhaseFlip]
    module
  have hdiagA : ‖⟪a, U a⟫_ℂ - (-1 : ℂ)‖ ≤ ‖U a - Z a‖ + 2 * ‖P a‖ := by
    have hv : U a + a = (U a - Z a) + (Z a + a) := by module
    calc
      ‖⟪a, U a⟫_ℂ - (-1 : ℂ)‖ = ‖⟪a, U a + a⟫_ℂ‖ := by
        rw [inner_add_right, haa]
        ring_nf
      _ ≤ ‖a‖ * ‖U a + a‖ := norm_inner_le_norm _ _
      _ = ‖U a + a‖ := by rw [ha, one_mul]
      _ = ‖(U a - Z a) + (Z a + a)‖ := by rw [hv]
      _ ≤ ‖U a - Z a‖ + ‖Z a + a‖ := norm_add_le _ _
      _ = ‖U a - Z a‖ + 2 * ‖P a‖ := by
        rw [hZa, norm_smul]
        norm_num
  have hdiagB : ‖⟪b, U b⟫_ℂ - (1 : ℂ)‖ ≤
      ‖U b - Z b‖ + 2 * ‖P b - b‖ := by
    have hv : U b - b = (U b - Z b) + (Z b - b) := by module
    calc
      ‖⟪b, U b⟫_ℂ - (1 : ℂ)‖ = ‖⟪b, U b - b⟫_ℂ‖ := by
        rw [inner_sub_right, hbb]
      _ ≤ ‖b‖ * ‖U b - b‖ := norm_inner_le_norm _ _
      _ = ‖U b - b‖ := by rw [hb, one_mul]
      _ = ‖(U b - Z b) + (Z b - b)‖ := by rw [hv]
      _ ≤ ‖U b - Z b‖ + ‖Z b - b‖ := norm_add_le _ _
      _ = ‖U b - Z b‖ + 2 * ‖P b - b‖ := by
        rw [hZb, norm_smul]
        norm_num
  have herr :
      ‖⟪a, U a⟫_ℂ - (-1 : ℂ)‖ + ‖⟪b, U b⟫_ℂ - (1 : ℂ)‖ ≤
        2 * ηj + ξ := by
    unfold ApproximatesRecordPhaseFlipOn at hread
    unfold ApproxRecordFor at hrecord
    linarith
  let x := ⟪a, U a⟫_ℂ
  let y := ⟪b, U b⟫_ℂ
  have htriangle : (2 : ℝ) ≤ ‖x - (-1 : ℂ)‖ + ‖x - y‖ + ‖y - (1 : ℂ)‖ := by
    have hnorm : ‖(-1 : ℂ) - 1‖ = 2 := by norm_num
    calc
      (2 : ℝ) = ‖(-1 : ℂ) - 1‖ := hnorm.symm
      _ = ‖((-1 : ℂ) - x) + (x - y) + (y - 1)‖ := by
        congr 1
        ring
      _ ≤ ‖((-1 : ℂ) - x) + (x - y)‖ + ‖y - 1‖ := norm_add_le _ _
      _ ≤ (‖(-1 : ℂ) - x‖ + ‖x - y‖) + ‖y - 1‖ := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right (norm_add_le ((-1 : ℂ) - x) (x - y)) ‖y - 1‖
      _ = ‖x - (-1 : ℂ)‖ + ‖x - y‖ + ‖y - 1‖ := by
        rw [show (-1 : ℂ) - x = -(x - (-1 : ℂ)) by ring, norm_neg]
  dsimp [x, y] at htriangle ⊢
  dsimp [U] at herr htriangle ⊢
  linarith

/-- The division-free threshold converts the quantitative diagonal-gap
estimate into the distinguishability proxy. -/
theorem approx_record_phase_flip_distinguishesAt
    {N d K : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (D : Circuit N d)
    (Λ : LabeledResolution (d ^ N) K) (j : Fin K)
    (a b : H (d ^ N)) (ηj ξ δ : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hrecord : ApproxRecordFor (rproj Λ j) b a ηj)
    (hread : ApproximatesRecordPhaseFlipOn e D Λ j a b ξ)
    (hthreshold : 2 * δ + 2 * ηj + ξ ≤ 2) :
    DistinguishesAt e a b δ D := by
  unfold DistinguishesAt
  have hgap := diagonal_gap_lower_bound_of_approx_phase_flip
    e D Λ j a b ηj ξ ha hb hrecord hread
  linarith

/-- The supplied approximate phase-readout circuit is an explicit
distinguishability upper-bound witness. -/
theorem approx_record_phase_flip_gives_upper_bound
    {N d K : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (D : Circuit N d)
    (Λ : LabeledResolution (d ^ N) K) (j : Fin K)
    (a b : H (d ^ N)) (ηj ξ δ : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hrecord : ApproxRecordFor (rproj Λ j) b a ηj)
    (hread : ApproximatesRecordPhaseFlipOn e D Λ j a b ξ)
    (hthreshold : 2 * δ + 2 * ηj + ξ ≤ 2) :
    HasDistinguishabilityUpperBound e a b δ (Circuit.length D) :=
  ⟨D, le_rfl, approx_record_phase_flip_distinguishesAt
    e D Λ j a b ηj ξ δ ha hb hrecord hread hthreshold⟩

/-- The same supplied readout circuit upper-bounds the actual minimum
distinguishability complexity. -/
theorem approx_record_phase_flip_complexity_upper_bound
    {N d K : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (D : Circuit N d)
    (Λ : LabeledResolution (d ^ N) K) (j : Fin K)
    (a b : H (d ^ N)) (ηj ξ δ : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hrecord : ApproxRecordFor (rproj Λ j) b a ηj)
    (hread : ApproximatesRecordPhaseFlipOn e D Λ j a b ξ)
    (hthreshold : 2 * δ + 2 * ηj + ξ ≤ 2) :
    distinguishabilityComplexity e a b δ ≤ (Circuit.length D : WithTop ℕ) := by
  apply complexity_le_of_distinguishabilityUpperBound
  exact approx_record_phase_flip_gives_upper_bound
    e D Λ j a b ηj ξ δ ha hb hrecord hread hthreshold

/-- Regression: zero record and readout errors reduce the approximate theorem
to the exact phase-flip threshold `2 * δ ≤ 2`. -/
theorem exact_record_phase_flip_distinguishesAt_via_approximation
    {N d K : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (D : Circuit N d)
    (Λ : LabeledResolution (d ^ N) K) (j : Fin K)
    (a b : H (d ^ N)) (δ : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hrecord : ApproxRecordFor (rproj Λ j) b a 0)
    (hD : ImplementsRecordPhaseFlip e D Λ j)
    (hthreshold : 2 * δ ≤ 2) :
    DistinguishesAt e a b δ D := by
  apply approx_record_phase_flip_distinguishesAt e D Λ j a b 0 0 δ ha hb hrecord
    (implementsRecordPhaseFlip_gives_approximation_zero e D Λ j a b hD)
  linarith

#print axioms approx_record_phase_flip_gives_upper_bound

end


end QuantumFoundations.Complexity
