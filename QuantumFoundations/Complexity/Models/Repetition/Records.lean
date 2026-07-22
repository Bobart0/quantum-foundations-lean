import QuantumFoundations.Complexity.Models.Repetition.States
import QuantumFoundations.Complexity.ApproxRecordBasic
import QuantumFoundations.Complexity.RecordInterference

/-!
# C9b — Explicit single-site redundant records

For site `r` and bit `b`, `sitesCell R r b` is spanned by the computational
basis configurations whose `r`-th bit is `b`.  The cell is transported once
to `H (2 ^ R)` to form the existing `LabeledResolution` API.  Its transported
record projector is exactly the original coordinate projector on `Sites`.
-/

namespace QuantumFoundations.Complexity.RepetitionModel

open scoped InnerProductSpace Classical

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

/-- Computational basis vector associated with a site configuration. -/
def configurationBasis {R : ℕ} (g : Fin R → Fin 2) : Sites R 2 :=
  EuclideanSpace.single g 1

/-- Configurations with prescribed bit `b` at site `r`. -/
def sitesCell (R : ℕ) (r : Fin R) (b : Fin 2) : Submodule ℂ (Sites R 2) :=
  Submodule.span ℂ (configurationBasis '' {g | g r = b})

theorem configurationBasis_mem_sitesCell {R : ℕ} (r : Fin R)
    (g : Fin R → Fin 2) : configurationBasis g ∈ sitesCell R r (g r) :=
  Submodule.subset_span ⟨g, rfl, rfl⟩

theorem sitesCell_ortho {R : ℕ} (r : Fin R) {b b' : Fin 2}
    (hbb : b ≠ b') : sitesCell R r b ⟂ sitesCell R r b' := by
  unfold sitesCell
  rw [Submodule.isOrtho_span]
  rintro u ⟨g, hg, rfl⟩ v ⟨k, hk, rfl⟩
  have hgk : g ≠ k := fun h => hbb (by rw [← hg, h, hk])
  unfold configurationBasis
  rw [EuclideanSpace.inner_single_left]
  simp [hgk.symm]

private theorem fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

theorem sitesCell_covers {R : ℕ} (r : Fin R) :
    sitesCell R r 0 ⊔ sitesCell R r 1 = ⊤ := by
  unfold sitesCell
  rw [← Submodule.span_union]
  have hunion :
      (configurationBasis '' {g : Fin R → Fin 2 | g r = 0}) ∪
          (configurationBasis '' {g : Fin R → Fin 2 | g r = 1}) =
        Set.range configurationBasis := by
    ext x
    simp only [Set.mem_union, Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro (⟨g, _, rfl⟩ | ⟨g, _, rfl⟩) <;> exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      rcases fin2_cases (g r) with h | h
      · exact Or.inl ⟨g, h, rfl⟩
      · exact Or.inr ⟨g, h, rfl⟩
  rw [hunion]
  have heq : configurationBasis =
      ⇑(EuclideanSpace.basisFun (Fin R → Fin 2) ℂ).toBasis := by
    funext g
    rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
    rfl
  rw [heq]
  exact (EuclideanSpace.basisFun (Fin R → Fin 2) ℂ).toBasis.span_eq

theorem sitesCell_iSup (R : ℕ) (r : Fin R) :
    (⨆ b : Fin 2, sitesCell R r b) = ⊤ := by
  rw [← Finset.sup_univ_eq_iSup]
  show ({0, 1} : Finset (Fin 2)).sup (sitesCell R r) = ⊤
  rw [Finset.sup_insert, Finset.sup_singleton, sitesCell_covers]

/-- The site cell transported back to the standard `H (2^R)` model. -/
def siteCell (R : ℕ) (r : Fin R) (b : Fin 2) : Submodule ℂ (H (2 ^ R)) :=
  (sitesCell R r b).map (sitesEquivR R).symm.toLinearEquiv.toLinearMap

/-- Binary computational resolution at a single record site. -/
def siteResolution (R : ℕ) (r : Fin R) : LabeledResolution (2 ^ R) 2 where
  cells := siteCell R r
  ortho := by
    intro i j hij
    apply Submodule.isOrtho_iff_le.mp
    exact (sitesCell_ortho r hij).map (sitesEquivR R).symm.toLinearIsometry
  covers := by
    unfold siteCell
    rw [← Submodule.map_iSup, sitesCell_iSup]
    rw [Submodule.map_top,
      LinearMap.range_eq_top.mpr (sitesEquivR R).symm.surjective]

/-- One singleton record region per site. -/
def repetitionRegions (R : ℕ) : Fin R → Finset (Fin R) := fun r => {r}

/-- The same binary label is recorded independently at every site. -/
def repetitionRecords (R : ℕ) : Fin R → LabeledResolution (2 ^ R) 2 :=
  siteResolution R

@[simp] theorem repetitionRegions_card {R : ℕ} (r : Fin R) :
    (repetitionRegions R r).card = 1 := by
  simp [repetitionRegions]

theorem repetitionRegions_pairwise_disjoint {R : ℕ} :
    ∀ r r' : Fin R, r ≠ r' →
      Disjoint (repetitionRegions R r) (repetitionRegions R r') := by
  intro r r' hrr'
  simp [repetitionRegions, hrr']

theorem sitesCell_starProjection_configurationBasis {R : ℕ}
    (r : Fin R) (b : Fin 2) (g : Fin R → Fin 2) :
    (sitesCell R r b).starProjection (configurationBasis g) =
      if g r = b then configurationBasis g else 0 := by
  split_ifs with h
  · exact Submodule.starProjection_eq_self_iff.mpr
      (h ▸ configurationBasis_mem_sitesCell r g)
  · rw [Submodule.starProjection_apply_eq_zero_iff]
    exact (sitesCell_ortho r (Ne.symm h)).symm
      (configurationBasis_mem_sitesCell r g)

/-- Transporting the record projector back to `Sites` recovers the explicit
coordinate-cell projector. -/
theorem transported_siteRecordProj_eq {R : ℕ} (r : Fin R) (b : Fin 2) :
    transportedRecordProj (sitesEquivR R) (siteResolution R r) b =
      (sitesCell R r b).starProjection.toLinearMap := by
  apply LinearMap.ext
  intro x
  change (sitesEquivR R)
      ((siteCell R r b).starProjection ((sitesEquivR R).symm x)) =
    (sitesCell R r b).starProjection x
  unfold siteCell
  rw [Submodule.starProjection_map_apply]
  simp

private theorem agreesOff_singleton_and_restriction_eq {R : ℕ}
    (r : Fin R) {g k : Fin R → Fin 2}
    (hoff : AgreesOff {r} g k)
    (hrest : g ∘ (Subtype.val : {x // x ∈ ({r} : Finset (Fin R))} → Fin R) =
      k ∘ Subtype.val) : g = k := by
  funext s
  by_cases hsr : s = r
  · subst s
    exact congrFun hrest ⟨r, by simp⟩
  · exact hoff s (by simpa using hsr)

theorem sitesCell_projection_local {R : ℕ} (r : Fin R) (b : Fin 2) :
    IsLocalTo (sitesCell R r b).starProjection.toLinearMap {r} := by
  let rr : {x // x ∈ ({r} : Finset (Fin R))} := ⟨r, by simp⟩
  refine ⟨fun gl kl => if kl rr = b ∧ gl = kl then 1 else 0, ?_⟩
  intro g k
  change ⟪configurationBasis g,
    (sitesCell R r b).starProjection (configurationBasis k)⟫_ℂ = _
  rw [sitesCell_starProjection_configurationBasis]
  by_cases hk : k r = b
  · rw [if_pos hk]
    by_cases hgk : g = k
    · subst g
      simp [configurationBasis, AgreesOff, rr, hk]
    · have hinner :
          ⟪configurationBasis g, configurationBasis k⟫_ℂ = 0 := by
        unfold configurationBasis
        rw [EuclideanSpace.inner_single_left]
        simp [hgk]
      rw [hinner]
      by_cases hoff : AgreesOff {r} g k
      · have hrest :
            g ∘ (Subtype.val : {x // x ∈ ({r} : Finset (Fin R))} → Fin R) ≠
              k ∘ Subtype.val := by
          intro h
          exact hgk (agreesOff_singleton_and_restriction_eq r hoff h)
        simp [hoff, hrest]
      · simp [hoff]
  · rw [if_neg hk]
    simp [hk, rr]

theorem siteRecordProj_local {R : ℕ} (r : Fin R) (b : Fin 2) :
    IsLocalTo
      (transportedRecordProj (sitesEquivR R) (repetitionRecords R r) b)
      (repetitionRegions R r) := by
  change IsLocalTo
    (transportedRecordProj (sitesEquivR R) (siteResolution R r) b) {r}
  rw [transported_siteRecordProj_eq]
  exact sitesCell_projection_local r b

theorem siteRecordProj_local_zero {R : ℕ} (r : Fin R) :
    IsLocalTo
      (transportedRecordProj (sitesEquivR R) (repetitionRecords R r) 0)
      (repetitionRegions R r) :=
  siteRecordProj_local r 0

theorem siteRecordProj_local_one {R : ℕ} (r : Fin R) :
    IsLocalTo
      (transportedRecordProj (sitesEquivR R) (repetitionRecords R r) 1)
      (repetitionRegions R r) :=
  siteRecordProj_local r 1

theorem siteProj_apply_configuration {R : ℕ} (r : Fin R) (b : Fin 2)
    (g : Fin R → Fin 2) :
    rproj (siteResolution R r) b ((sitesEquivR R).symm (configurationBasis g)) =
      if g r = b then (sitesEquivR R).symm (configurationBasis g) else 0 := by
  change (siteCell R r b).starProjection ((sitesEquivR R).symm (configurationBasis g)) = _
  unfold siteCell
  rw [Submodule.starProjection_map_apply]
  simp only [LinearIsometryEquiv.symm_apply_apply]
  rw [sitesCell_starProjection_configurationBasis]
  split_ifs <;> simp_all

theorem siteProj_zero_fixes_zeroBranch {R : ℕ} (r : Fin R) :
    rproj (siteResolution R r) 0 (zeroBranch R) = zeroBranch R := by
  simpa [zeroBranch, sitesZero, configurationBasis, zeroConfiguration] using
    siteProj_apply_configuration r 0 (zeroConfiguration R)

theorem siteProj_zero_kills_oneBranch {R : ℕ} (r : Fin R) :
    rproj (siteResolution R r) 0 (oneBranch R) = 0 := by
  simpa [oneBranch, sitesOne, configurationBasis, oneConfiguration] using
    siteProj_apply_configuration r 0 (oneConfiguration R)

theorem siteProj_one_fixes_oneBranch {R : ℕ} (r : Fin R) :
    rproj (siteResolution R r) 1 (oneBranch R) = oneBranch R := by
  simpa [oneBranch, sitesOne, configurationBasis, oneConfiguration] using
    siteProj_apply_configuration r 1 (oneConfiguration R)

theorem siteProj_one_kills_zeroBranch {R : ℕ} (r : Fin R) :
    rproj (siteResolution R r) 1 (zeroBranch R) = 0 := by
  simpa [zeroBranch, sitesZero, configurationBasis, zeroConfiguration] using
    siteProj_apply_configuration r 1 (zeroConfiguration R)

theorem repetitionState_isRecordedOn (R : ℕ) [NeZero R] :
    IsRecordedOn (repetitionState R) (repetitionRecords R) := by
  intro r r' b
  rcases fin2_cases b with rfl | rfl
  · simp only [repetitionRecords, repetitionState, map_add, siteProj_zero_fixes_zeroBranch,
      siteProj_zero_kills_oneBranch, add_zero]
  · simp only [repetitionRecords, repetitionState, map_add, siteProj_one_kills_zeroBranch,
      siteProj_one_fixes_oneBranch, zero_add]

theorem repetition_branch_zero (R : ℕ) [NeZero R] :
    branch (repetitionRecords R) (repetitionState R) 0 = zeroBranch R := by
  change rproj (siteResolution R 0) 0 (repetitionState R) = zeroBranch R
  simp only [repetitionState, map_add, siteProj_zero_fixes_zeroBranch,
    siteProj_zero_kills_oneBranch, add_zero]

theorem repetition_branch_one (R : ℕ) [NeZero R] :
    branch (repetitionRecords R) (repetitionState R) 1 = oneBranch R := by
  change rproj (siteResolution R 0) 1 (repetitionState R) = oneBranch R
  simp only [repetitionState, map_add, siteProj_one_kills_zeroBranch,
    siteProj_one_fixes_oneBranch, zero_add]

theorem repetition_approxRecordedPair_zero (R : ℕ) [NeZero R] :
    ApproxRecordedPairOn (repetitionRecords R)
      (zeroBranch R) (oneBranch R) 0 1 0 0 := by
  intro r
  constructor
  · exact approxRecordFor_zero_of_fixes_rejects
      (by simpa [repetitionRecords] using siteProj_zero_fixes_zeroBranch r)
      (by simpa [repetitionRecords] using siteProj_zero_kills_oneBranch r)
  · exact approxRecordFor_zero_of_fixes_rejects
      (by simpa [repetitionRecords] using siteProj_one_fixes_oneBranch r)
      (by simpa [repetitionRecords] using siteProj_one_kills_zeroBranch r)

theorem normalized_repetition_branch_zero (R : ℕ) [NeZero R] :
    normalizedBranch (repetitionRecords R) (repetitionState R) 0 = zeroBranch R := by
  rw [normalizedBranch_eq_smul_branch, repetition_branch_zero, zeroBranch_norm]
  norm_num

theorem normalized_repetition_branch_one (R : ℕ) [NeZero R] :
    normalizedBranch (repetitionRecords R) (repetitionState R) 1 = oneBranch R := by
  rw [normalizedBranch_eq_smul_branch, repetition_branch_one, oneBranch_norm]
  norm_num

#print axioms repetitionState_isRecordedOn

end

end QuantumFoundations.Complexity.RepetitionModel
