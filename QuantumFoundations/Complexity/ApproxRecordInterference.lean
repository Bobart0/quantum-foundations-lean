import QuantumFoundations.Complexity.ApproxRecordBasic
import QuantumFoundations.Complexity.ProxyTransport

/-!
# C8b — Untouched approximate records bound cross amplitudes

The analytic estimate is first stated for an arbitrary symmetric operator
commuting with circuit evaluation.  The aggregate error is sharp for this
argument: Cauchy–Schwarz produces exactly the fixing defect plus the rejected
state leakage, with no additional factor.
-/

namespace QuantumFoundations.Complexity

open scoped InnerProductSpace

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

/-- A symmetric approximate-record operator commuting with a unitary circuit
bounds the corresponding cross amplitude by its aggregate record error. -/
theorem norm_cross_amplitude_le_of_approx_record
    {N d : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (C : Circuit N d)
    (P : H (d ^ N) →ₗ[ℂ] H (d ^ N)) (a b : H (d ^ N)) (η : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hsymm : LinearMap.IsSymmetric P)
    (hcomm : Commute (Circuit.evalOnH C e) P)
    (happrox : ApproxRecordFor P b a η) :
    ‖⟪b, Circuit.evalOnH C e a⟫_ℂ‖ ≤ η := by
  let V := Circuit.evalOnH C e
  have hsplit : b = P b + (b - P b) := by module
  have hcomm_apply : P (V a) = V (P a) := (commute_apply hcomm a).symm
  have hfirst : ‖⟪P b, V a⟫_ℂ‖ ≤ ‖P a‖ := by
    rw [hsymm b (V a), hcomm_apply]
    calc
      ‖⟪b, V (P a)⟫_ℂ‖ ≤ ‖b‖ * ‖V (P a)‖ := norm_inner_le_norm _ _
      _ = ‖P a‖ := by rw [hb, Circuit.evalOnH_norm]; simp
  have hsecond : ‖⟪b - P b, V a⟫_ℂ‖ ≤ ‖P b - b‖ := by
    calc
      ‖⟪b - P b, V a⟫_ℂ‖ ≤ ‖b - P b‖ * ‖V a‖ := norm_inner_le_norm _ _
      _ = ‖b - P b‖ := by rw [Circuit.evalOnH_norm, ha, mul_one]
      _ = ‖P b - b‖ := by
        rw [show b - P b = -(P b - b) by module, norm_neg]
  rw [hsplit, inner_add_left]
  calc
    ‖⟪P b, V a⟫_ℂ + ⟪b - P b, V a⟫_ℂ‖ ≤
        ‖⟪P b, V a⟫_ℂ‖ + ‖⟪b - P b, V a⟫_ℂ‖ := norm_add_le _ _
    _ ≤ ‖P a‖ + ‖P b - b‖ := add_le_add hfirst hsecond
    _ = ‖P b - b‖ + ‖P a‖ := add_comm _ _
    _ ≤ η := happrox

/-- Public record-projector specialization: if the record region is untouched,
its target/source cross amplitude is bounded by the aggregate record error. -/
theorem norm_cross_amplitude_le_of_untouched_approx_record
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (C : Circuit N d)
    (regions : Fin R → Finset (Fin N))
    (recs : Fin R → LabeledResolution (d ^ N) K)
    (r : Fin R) (j : Fin K) (a b : H (d ^ N)) (η : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hlocal : IsLocalTo (transportedRecordProj e (recs r) j) (regions r))
    (hdisj : Disjoint (Circuit.support C) (regions r))
    (happrox : ApproxRecordFor (rproj (recs r) j) b a η) :
    ‖⟪b, Circuit.evalOnH C e a⟫_ℂ‖ ≤ η := by
  apply norm_cross_amplitude_le_of_approx_record e C
    (rproj (recs r) j) a b η ha hb
  · intro x y
    exact Submodule.starProjection_isSymmetric ((recs r).cells j) x y
  · exact evalOnH_commute_recordProj e C (regions r) (recs r) j hlocal hdisj
  · exact happrox

/-- If neither label's record region is touched, the complete two-orientation
interference expression is at most the sum of the two aggregate errors. -/
theorem interference_expression_le_of_untouched_approx_records
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (C : Circuit N d)
    (regions : Fin R → Finset (Fin N))
    (recs : Fin R → LabeledResolution (d ^ N) K)
    (a b : H (d ^ N)) (i j : Fin K) (ηi ηj : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (happrox : ApproxRecordedPairOn recs a b i j ηi ηj)
    (hlocal_i : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) i) (regions r))
    (hlocal_j : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) j) (regions r))
    (r : Fin R) (hdisj : Disjoint (Circuit.support C) (regions r)) :
    ‖⟪a, Circuit.evalOnH C e b⟫_ℂ‖ +
        ‖⟪b, Circuit.evalOnH C e a⟫_ℂ‖ ≤ ηi + ηj := by
  exact add_le_add
    (norm_cross_amplitude_le_of_untouched_approx_record
      e C regions recs r i b a ηi hb ha (hlocal_i r) hdisj (happrox r).1)
    (norm_cross_amplitude_le_of_untouched_approx_record
      e C regions recs r j a b ηj ha hb (hlocal_j r) hdisj (happrox r).2)

/-- Zero aggregate errors recover exact vanishing of both cross amplitudes on
an untouched record region. -/
theorem cross_amplitudes_eq_zero_of_untouched_zero_error_records
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (C : Circuit N d)
    (regions : Fin R → Finset (Fin N))
    (recs : Fin R → LabeledResolution (d ^ N) K)
    (a b : H (d ^ N)) (i j : Fin K)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (happrox : ApproxRecordedPairOn recs a b i j 0 0)
    (hlocal_i : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) i) (regions r))
    (hlocal_j : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) j) (regions r))
    (r : Fin R) (hdisj : Disjoint (Circuit.support C) (regions r)) :
    ⟪a, Circuit.evalOnH C e b⟫_ℂ = 0 ∧
      ⟪b, Circuit.evalOnH C e a⟫_ℂ = 0 := by
  have h := interference_expression_le_of_untouched_approx_records
    e C regions recs a b i j 0 0 ha hb happrox hlocal_i hlocal_j r hdisj
  have hab : ‖⟪a, Circuit.evalOnH C e b⟫_ℂ‖ = 0 := by
    have hnonneg := norm_nonneg ⟪b, Circuit.evalOnH C e a⟫_ℂ
    simp only [add_zero] at h
    exact le_antisymm (by linarith) (norm_nonneg _)
  have hba : ‖⟪b, Circuit.evalOnH C e a⟫_ℂ‖ = 0 := by
    have hnonneg := norm_nonneg ⟪a, Circuit.evalOnH C e b⟫_ℂ
    simp only [add_zero] at h
    exact le_antisymm (by linarith) (norm_nonneg _)
  exact ⟨norm_eq_zero.mp hab, norm_eq_zero.mp hba⟩

#print axioms norm_cross_amplitude_le_of_untouched_approx_record

end


end QuantumFoundations.Complexity
