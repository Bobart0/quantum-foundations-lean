import QuantumFoundations.Complexity.BranchGap

/-!
# C6 — Exact minimum circuit complexities

Only after the relational certificates are complete do we package circuit
lengths as infima in `WithTop ℕ`.  An unsatisfied predicate has value `⊤`.
No attainment theorem and no subtraction on `WithTop ℕ` is needed.
-/

namespace QuantumFoundations.Complexity

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

/-- The infimum of the lengths of circuits satisfying `P`, with nonsatisfying
circuits contributing `⊤`.  Consequently, an empty predicate has value
`⊤`. -/
noncomputable def minCircuitLength {N d : ℕ}
    (P : Circuit N d → Prop) : WithTop ℕ := by
  classical
  exact ⨅ C, if P C then (Circuit.length C : WithTop ℕ) else ⊤

/-- Any satisfying circuit gives an upper bound on the minimum length. -/
theorem minCircuitLength_le_of_witness {N d : ℕ}
    {P : Circuit N d → Prop} (C : Circuit N d) (hC : P C) :
    minCircuitLength P ≤ (Circuit.length C : WithTop ℕ) := by
  apply iInf_le_of_le C
  simp [hC]

/-- A uniform lower bound for all satisfying circuits bounds the minimum. -/
theorem le_minCircuitLength_of_forall {N d : ℕ}
    {P : Circuit N d → Prop} {B : ℕ}
    (h : ∀ C, P C → B ≤ Circuit.length C) :
    (B : WithTop ℕ) ≤ minCircuitLength P := by
  apply le_iInf
  intro C
  by_cases hC : P C
  · simp only [hC, if_true]
    exact_mod_cast h C hC
  · simp [hC]

/-- Predicate inclusion reverses the corresponding minimum inequality:
more admissible circuits can only lower the infimum. -/
theorem minCircuitLength_mono {N d : ℕ}
    {P Q : Circuit N d → Prop} (hPQ : ∀ C, P C → Q C) :
    minCircuitLength Q ≤ minCircuitLength P := by
  apply le_iInf
  intro C
  by_cases hC : P C
  · exact (minCircuitLength_le_of_witness C (hPQ C hC)).trans_eq (by
      simp [hC])
  · simp [hC]

/-- With no satisfying circuit, the minimum length is `⊤`. -/
theorem minCircuitLength_eq_top_of_no_witness {N d : ℕ}
    {P : Circuit N d → Prop} (h : ∀ C, ¬ P C) :
    minCircuitLength P = ⊤ := by
  apply top_unique
  apply le_iInf
  intro C
  simp [h C]

/-- A satisfying circuit makes the minimum finite. -/
theorem minCircuitLength_ne_top_of_witness {N d : ℕ}
    {P : Circuit N d → Prop} (C : Circuit N d) (hC : P C) :
    minCircuitLength P ≠ ⊤ :=
  ne_top_of_le_ne_top WithTop.coe_ne_top
    (minCircuitLength_le_of_witness C hC)

/-- Exact interference complexity proxy as a `WithTop ℕ` minimum. -/
noncomputable def interferenceComplexity {N d : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N)) (δ : ℝ) :
    WithTop ℕ :=
  minCircuitLength (InterferesAt e a b δ)

/-- Exact distinguishability complexity proxy as a `WithTop ℕ` minimum. -/
noncomputable def distinguishabilityComplexity {N d : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N)) (δ : ℝ) :
    WithTop ℕ :=
  minCircuitLength (DistinguishesAt e a b δ)

/-- Relational interference lower bounds transfer directly to the minimum
complexity. -/
theorem interferenceLowerBound_le_complexity {N d : ℕ}
    {e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d} {a b : H (d ^ N)} {δ : ℝ} {B : ℕ}
    (h : HasInterferenceLowerBound e a b δ B) :
    (B : WithTop ℕ) ≤ interferenceComplexity e a b δ := by
  exact le_minCircuitLength_of_forall h

/-- A relational distinguishability witness transfers directly to an upper
bound on the minimum complexity. -/
theorem complexity_le_of_distinguishabilityUpperBound {N d : ℕ}
    {e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d} {a b : H (d ^ N)} {δ : ℝ} {D : ℕ}
    (h : HasDistinguishabilityUpperBound e a b δ D) :
    distinguishabilityComplexity e a b δ ≤ (D : WithTop ℕ) := by
  obtain ⟨C, hlen, hC⟩ := h
  calc
    distinguishabilityComplexity e a b δ
        ≤ (Circuit.length C : WithTop ℕ) := minCircuitLength_le_of_witness C hC
    _ ≤ (D : WithTop ℕ) := by exact_mod_cast hlen

/-- Exact redundant records lower-bound the actual `WithTop ℕ` interference
complexity by `ceilHalf R`. -/
theorem redundant_records_interferenceComplexity_lower_bound
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (regions : Fin R → Finset (Fin N))
    (recs : Fin R → LabeledResolution (d ^ N) K) (ψ : H (d ^ N))
    (hrec : IsRecordedOn ψ recs) (i j : Fin K) (hij : i ≠ j)
    (hi : branch recs ψ i ≠ 0) (hj : branch recs ψ j ≠ 0)
    (hlocal_i : ∀ r, IsLocalTo (transportedRecordProj e (recs r) i) (regions r))
    (hlocal_j : ∀ r, IsLocalTo (transportedRecordProj e (recs r) j) (regions r))
    (hpairwise : ∀ r r', r ≠ r' → Disjoint (regions r) (regions r'))
    (δ : ℝ) (hδ : 0 < δ) :
    (ceilHalf R : WithTop ℕ) ≤ interferenceComplexity e
      (normalizedBranch recs ψ i) (normalizedBranch recs ψ j) δ := by
  apply interferenceLowerBound_le_complexity
  exact redundant_records_give_interference_lower_bound
    e regions recs ψ hrec i j hij hi hj hlocal_i hlocal_j hpairwise δ hδ

/-- An explicit exact record phase-flip circuit upper-bounds the actual
`WithTop ℕ` distinguishability complexity by its length. -/
theorem record_phase_flip_distinguishabilityComplexity_upper_bound
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (recs : Fin R → LabeledResolution (d ^ N) K) (ψ : H (d ^ N))
    (hrec : IsRecordedOn ψ recs) (r₀ : Fin R) (i j : Fin K)
    (hij : i ≠ j) (hi : branch recs ψ i ≠ 0) (hj : branch recs ψ j ≠ 0)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (D : Circuit N d) (hD : ImplementsRecordPhaseFlip e D (recs r₀) j) :
    distinguishabilityComplexity e
      (normalizedBranch recs ψ i) (normalizedBranch recs ψ j) δ
      ≤ (Circuit.length D : WithTop ℕ) := by
  apply complexity_le_of_distinguishabilityUpperBound
  exact record_phase_flip_gives_distinguishability_upper_bound
    e recs ψ hrec r₀ i j hij hi hj δ hδ0 hδ1 D hD

/-- Exact subtraction-free complexity gap from redundant records and a
supplied record-readout circuit. -/
theorem redundant_records_complexity_gap
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
    distinguishabilityComplexity e
        (normalizedBranch recs ψ i) (normalizedBranch recs ψ j) δ +
        (g : WithTop ℕ)
      ≤ interferenceComplexity e
        (normalizedBranch recs ψ i) (normalizedBranch recs ψ j) δ := by
  have hDupper := record_phase_flip_distinguishabilityComplexity_upper_bound
    e recs ψ hrec r₀ i j hij hi hj δ hδ0.le hδ1 D hD
  have hIlower := redundant_records_interferenceComplexity_lower_bound
    e regions recs ψ hrec i j hij hi hj hlocal_i hlocal_j hpairwise δ hδ0
  calc
    distinguishabilityComplexity e
          (normalizedBranch recs ψ i) (normalizedBranch recs ψ j) δ +
          (g : WithTop ℕ)
        ≤ (Circuit.length D : WithTop ℕ) + (g : WithTop ℕ) :=
      add_le_add hDupper le_rfl
    _ = ((Circuit.length D + g : ℕ) : WithTop ℕ) := by norm_num
    _ ≤ (ceilHalf R : WithTop ℕ) := by exact_mod_cast hgap
    _ ≤ interferenceComplexity e
          (normalizedBranch recs ψ i) (normalizedBranch recs ψ j) δ := hIlower

#print axioms redundant_records_complexity_gap

end

end QuantumFoundations.Complexity
