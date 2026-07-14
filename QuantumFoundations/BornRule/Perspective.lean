import QuantumFoundations.Wigner.Main

/-!
# B1 — Scaffolding : perspectives, axiomes, Lemme 4 (Définitions 1-3, Lemmes 1-4)

Port de `theorem1_general_en.lean` (dépôt `tstar-born-rule-lean`), REFORMULÉ
directement pour `V := H n` plutôt que gardé sur un espace abstrait (décision
de reconnaissance B0) : `Gleason.gleason`, utilisé en `BornRule/GleasonBridge.lean`,
est spécifique à `H n`, et aucun cas d'usage actuel ne réclame la généralité
d'un espace `V` quelconque. Bénéfice immédiat : `Module.finrank ℂ (H n) = n`
(simp), donc les bases de l'espace ENTIER s'indexent directement par `Fin n`
plutôt que par `Fin (Module.finrank ℂ V)` — élimine une couche de cast pour
`basisPerspective`/`line_ne_bot`/`line_ne_top`/`line_injective`. Les bases
d'une cellule `c` quelconque (`cellLines`, dimension variable) gardent
nécessairement `Fin (Module.finrank ℂ c)`.

**Zéro but ouvert, y compris en position de repli** (contrairement à
`theorem1_general_en.lean`, qui en laisse deux non fermés) : les deux replis
(`Perspective.binary.span`, `basisPerspective.span`) se referment directement
avec `H n`, respectivement via `Submodule.sup_orthogonal_of_hasOrthogonalProjection`
(instance `HasOrthogonalProjection` automatique en dimension finie) et
`Submodule.span_range_eq_iSup` (déjà exploité côté `Gleason.ProjMeasure.
isCFrameFunction`) — aucune reconstruction, juste suppression du repli.
-/

namespace QuantumFoundations.BornRule

open scoped InnerProductSpace
open scoped Classical
open Gleason

noncomputable section

variable {n : ℕ}

/-- A perspective: a finite family of pairwise orthogonal, non-zero
    subspaces of `H n` whose supremum is the whole space (Définition 1). -/
structure Perspective (n : ℕ) where
  cells : Finset (Submodule ℂ (H n))
  nz    : ∀ c ∈ cells, c ≠ ⊥
  ortho : ∀ c ∈ cells, ∀ c' ∈ cells, c ≠ c' → c ≤ c'ᗮ
  span  : sSup (cells : Set (Submodule ℂ (H n))) = ⊤

/-- Refinement: every fine cell is contained in some coarse cell
    (Définition 2). -/
def Refines (D' D : Perspective n) : Prop :=
  ∀ c' ∈ D'.cells, ∃ c ∈ D.cells, c' ≤ c

namespace Perspective

/-- Unique parent (Lemme 1) : a non-zero subspace cannot be contained
    in two distinct cells of the same perspective. -/
theorem unique_parent (D : Perspective n) {c₁ c₂ K : Submodule ℂ (H n)}
    (h₁ : c₁ ∈ D.cells) (h₂ : c₂ ∈ D.cells) (hK : K ≠ ⊥)
    (hK₁ : K ≤ c₁) (hK₂ : K ≤ c₂) : c₁ = c₂ := by
  by_contra hne
  apply hK
  apply (Submodule.eq_bot_iff K).mpr
  intro x hx
  have hxc1 : x ∈ c₁ := hK₁ hx
  have hxc2 : x ∈ c₂ := hK₂ hx
  have hxc1perp : x ∈ c₁ᗮ := D.ortho c₂ h₂ c₁ h₁ (Ne.symm hne) hxc2
  have hz : ⟪x, x⟫_ℂ = 0 := (Submodule.mem_orthogonal c₁ x).mp hxc1perp x hxc1
  exact inner_self_eq_zero.mp hz

/-- The binary decomposition `{K, Kᗮ}` (Lemme 2) is a legitimate
    perspective, for any proper non-zero subspace `K`. -/
noncomputable def binary (K : Submodule ℂ (H n)) (h1 : K ≠ ⊥) (h2 : K ≠ ⊤) :
    Perspective n where
  cells := {K, Kᗮ}
  nz := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact h1
    · intro hbot
      apply h2
      have h : Kᗮᗮ = (⊥ : Submodule ℂ (H n))ᗮ := congrArg Submodule.orthogonal hbot
      rwa [Submodule.orthogonal_orthogonal, Submodule.bot_orthogonal_eq_top] at h
  ortho := by
    intro c hc c' hc' hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc hc'
    rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl <;>
      first
        | exact absurd rfl hne
        | exact le_refl _
        | exact Submodule.le_orthogonal_orthogonal _
  span := by
    show sSup (({K, Kᗮ} : Finset (Submodule ℂ (H n))) : Set (Submodule ℂ (H n))) = ⊤
    rw [Finset.coe_insert, Finset.coe_singleton, sSup_insert, sSup_singleton]
    exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

/-- If `⊤` belongs to a perspective, that perspective reduces to the
    singleton `{⊤}`. -/
theorem singleton_of_mem_top (D : Perspective n) (hD : (⊤ : Submodule ℂ (H n)) ∈ D.cells) :
    D.cells = {⊤} := by
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hD, fun c' hc' => ?_⟩
  by_contra hne
  have hle : c' ≤ (⊤ : Submodule ℂ (H n))ᗮ := D.ortho c' hc' ⊤ hD hne
  have htopperp : (⊤ : Submodule ℂ (H n))ᗮ = ⊥ := by
    have h : (⊥ᗮᗮ : Submodule ℂ (H n)) = (⊤ : Submodule ℂ (H n))ᗮ :=
      congrArg Submodule.orthogonal Submodule.bot_orthogonal_eq_top
    rw [Submodule.orthogonal_orthogonal] at h
    exact h.symm
  rw [htopperp] at hle
  exact D.nz c' hc' (le_bot_iff.mp hle)

end Perspective

-- An estimation rule: a real weight per (perspective, cell) pair.
variable (Est : Perspective n → Submodule ℂ (H n) → ℝ)

/-- (Grain) : coherence of the estimation rule under refinement
    (Définition 3, premier axiome). -/
def AxGrain : Prop :=
  ∀ D' D : Perspective n, Refines D' D →
    ∀ c ∈ D.cells, Est D c = ∑ c' ∈ D'.cells.filter (· ≤ c), Est D' c'

/-- (Norm) : normalisation over any perspective. -/
def AxNorm : Prop := ∀ D : Perspective n, ∑ c ∈ D.cells, Est D c = 1

/-- (Pos) : positivity of the estimation rule. -/
def AxPos : Prop := ∀ D : Perspective n, ∀ c ∈ D.cells, 0 ≤ Est D c

/-- (Null) : a cell orthogonal to a fixed unit vector `v` carries no
    weight. -/
def AxNul (v : H n) : Prop := ∀ D : Perspective n, ∀ c ∈ D.cells, v ∈ cᗮ → Est D c = 0

/-- **Lemme 4** : under (Grain) alone, the weight of a cell shared by
    two perspectives does not depend on which perspective it is
    evaluated in. Non-contextuality, usually postulated in
    Gleason-type derivations, is here a consequence of grain coherence
    alone — 0 axiome externe (Section 4 du papier). -/
theorem lemma4_noncontextual (hA : AxGrain Est) (hN : AxNorm Est)
    {D₁ D₂ : Perspective n} {c : Submodule ℂ (H n)}
    (h₁ : c ∈ D₁.cells) (h₂ : c ∈ D₂.cells) :
    Est D₁ c = Est D₂ c := by
  by_cases htop : c = ⊤
  · subst htop
    have e1 : D₁.cells = {⊤} := D₁.singleton_of_mem_top h₁
    have e2 : D₂.cells = {⊤} := D₂.singleton_of_mem_top h₂
    have s1 := hN D₁
    have s2 := hN D₂
    rw [e1, Finset.sum_singleton] at s1
    rw [e2, Finset.sum_singleton] at s2
    rw [s1, s2]
  · have hcne : c ≠ ⊥ := fun hbot => D₁.nz c h₁ hbot
    let D₀ := Perspective.binary c hcne htop
    have hcellsD0 : D₀.cells = insert c {cᗮ} := rfl
    have hmem0 : c ∈ D₀.cells := by
      rw [hcellsD0]; exact Finset.mem_insert_self _ _
    have hraf1 : Refines D₁ D₀ := by
      intro c' hc'
      by_cases heq : c' = c
      · exact ⟨c, hmem0, heq ▸ le_refl c⟩
      · refine ⟨cᗮ, ?_, D₁.ortho c' hc' c h₁ heq⟩
        rw [hcellsD0]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hraf2 : Refines D₂ D₀ := by
      intro c' hc'
      by_cases heq : c' = c
      · exact ⟨c, hmem0, heq ▸ le_refl c⟩
      · refine ⟨cᗮ, ?_, D₂.ortho c' hc' c h₂ heq⟩
        rw [hcellsD0]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have key1 : Est D₀ c = Est D₁ c := by
      have heq := hA D₁ D₀ hraf1 c hmem0
      rw [heq]
      have hfilter : D₁.cells.filter (· ≤ c) = {c} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨Finset.mem_filter.mpr ⟨h₁, le_refl c⟩, fun c' hc' => ?_⟩
        obtain ⟨hc'mem, hc'le⟩ := Finset.mem_filter.mp hc'
        exact D₁.unique_parent hc'mem h₁ (D₁.nz c' hc'mem) (le_refl c') hc'le
      rw [hfilter, Finset.sum_singleton]
    have key2 : Est D₀ c = Est D₂ c := by
      have heq := hA D₂ D₀ hraf2 c hmem0
      rw [heq]
      have hfilter : D₂.cells.filter (· ≤ c) = {c} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨Finset.mem_filter.mpr ⟨h₂, le_refl c⟩, fun c' hc' => ?_⟩
        obtain ⟨hc'mem, hc'le⟩ := Finset.mem_filter.mp hc'
        exact D₂.unique_parent hc'mem h₂ (D₂.nz c' hc'mem) (le_refl c') hc'le
      rw [hfilter, Finset.sum_singleton]
    rw [← key1, key2]

/-- The line spanned by a vector of an orthonormal basis of `H n` is
    never zero. -/
theorem line_ne_bot (b : OrthonormalBasis (Fin n) ℂ (H n)) (i : Fin n) :
    (ℂ ∙ (b i : H n)) ≠ ⊥ := by
  have hbi_ne : (b i : H n) ≠ 0 := by
    have hnorm : ‖(b i : H n)‖ = 1 := b.orthonormal.1 i
    intro hzero
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  rw [Submodule.ne_bot_iff]
  exact ⟨b i, Submodule.mem_span_singleton_self _, hbi_ne⟩

/-- The same line is never the whole space, as soon as `n ≥ 2`. -/
theorem line_ne_top (hn2 : 2 ≤ n) (b : OrthonormalBasis (Fin n) ℂ (H n)) (i : Fin n) :
    (ℂ ∙ (b i : H n)) ≠ ⊤ := by
  intro htop
  have hbi_ne : (b i : H n) ≠ 0 := by
    have hnorm : ‖(b i : H n)‖ = 1 := b.orthonormal.1 i
    intro hzero
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  have h1 : Module.finrank ℂ (ℂ ∙ (b i : H n)) = 1 := finrank_span_singleton hbi_ne
  rw [htop] at h1
  have h2 : Module.finrank ℂ (⊤ : Submodule ℂ (H n)) = n := by
    rw [finrank_top]; simp
  rw [h2] at h1
  omega

/-- The map sending an index to the line spanned by the corresponding
    basis vector is injective. -/
theorem line_injective (b : OrthonormalBasis (Fin n) ℂ (H n)) :
    Set.InjOn (fun i => (ℂ ∙ (b i : H n) : Submodule ℂ (H n))) (↑(Finset.univ : Finset (Fin n))) := by
  intro i _ j _ heq
  by_contra hij
  have hbi_ne : (b i : H n) ≠ 0 := by
    have hnorm : ‖(b i : H n)‖ = 1 := b.orthonormal.1 i
    intro hzero; rw [hzero, norm_zero] at hnorm; norm_num at hnorm
  have hbi_mem : (b i : H n) ∈ (ℂ ∙ (b j : H n)) := by
    have heq' : (ℂ ∙ (b i : H n) : Submodule ℂ (H n)) = ℂ ∙ (b j : H n) := heq
    rw [← heq']
    exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hbi_mem
  have horth : (⟪(b j : H n), (b i : H n)⟫_ℂ) = 0 := by
    have h1 : (⟪(b i : H n), (b j : H n)⟫_ℂ) = 0 := b.orthonormal.2 hij
    have h2 : (⟪(b j : H n), (b i : H n)⟫_ℂ) = starRingEnd ℂ (⟪(b i : H n), (b j : H n)⟫_ℂ) :=
      (inner_conj_symm (b j : H n) (b i : H n)).symm
    rw [h2, h1]; simp
  have hbjbj : (⟪(b j : H n), (b j : H n)⟫_ℂ) = 1 := by
    have hn : ‖(b j : H n)‖ = 1 := b.orthonormal.1 j
    have heq := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (b j : H n)
    rw [heq, hn]; norm_num
  rw [← hc, inner_smul_right, hbjbj, mul_one] at horth
  exact hbi_ne (by rw [← hc, horth, zero_smul])

/-- A whole orthonormal basis defines a perspective. -/
noncomputable def basisPerspective (b : OrthonormalBasis (Fin n) ℂ (H n)) : Perspective n where
  cells := Finset.univ.image (fun i => ℂ ∙ (b i : H n))
  nz := by
    intro c hc
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hc
    obtain ⟨i, rfl⟩ := hc
    exact line_ne_bot b i
  ortho := by
    intro c hc c' hc' hne
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hc hc'
    obtain ⟨i, rfl⟩ := hc
    obtain ⟨j, rfl⟩ := hc'
    have hij : i ≠ j := fun h => hne (by rw [h])
    have horth : (⟪(b j : H n), (b i : H n)⟫_ℂ) = 0 := by
      have h1 : (⟪(b i : H n), (b j : H n)⟫_ℂ) = 0 := b.orthonormal.2 hij
      have h2 : (⟪(b j : H n), (b i : H n)⟫_ℂ) = starRingEnd ℂ (⟪(b i : H n), (b j : H n)⟫_ℂ) :=
        (inner_conj_symm (b j : H n) (b i : H n)).symm
      rw [h2, h1]; simp
    rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [inner_smul_left, horth, mul_zero]
  span := by
    show sSup ((Finset.univ.image (fun i => ℂ ∙ (b i : H n))) : Set (Submodule ℂ (H n))) = ⊤
    have himg : ((Finset.univ.image (fun i => ℂ ∙ (b i : H n))) : Set (Submodule ℂ (H n)))
        = Set.range (fun i => ℂ ∙ (b i : H n)) := by
      ext c
      simp [Set.mem_range]
    rw [himg, sSup_range, ← Submodule.span_range_eq_iSup]
    exact b.toBasis.span_eq

/-- Lines from an orthonormal basis relative to a single cell `c`
    (rather than to the whole space): generalises `basisPerspective`
    to an arbitrary subspace. -/
noncomputable def cellLines (c : Submodule ℂ (H n)) : Finset (Submodule ℂ (H n)) :=
  Finset.univ.image (fun i : Fin (Module.finrank ℂ c) => ℂ ∙ ((stdOrthonormalBasis ℂ c i : c) : H n))

theorem cellLines_le (c : Submodule ℂ (H n)) : ∀ x ∈ cellLines c, x ≤ c := by
  intro x hx
  simp only [cellLines, Finset.mem_image, Finset.mem_univ, true_and] at hx
  obtain ⟨i, rfl⟩ := hx
  rw [Submodule.span_singleton_le_iff_mem]
  exact SetLike.coe_mem _

theorem cellLines_ne_bot (c : Submodule ℂ (H n)) : ∀ x ∈ cellLines c, x ≠ ⊥ := by
  intro x hx
  simp only [cellLines, Finset.mem_image, Finset.mem_univ, true_and] at hx
  obtain ⟨i, rfl⟩ := hx
  rw [Submodule.ne_bot_iff]
  refine ⟨(stdOrthonormalBasis ℂ c i : c), Submodule.mem_span_singleton_self _, ?_⟩
  have hnorm : ‖(stdOrthonormalBasis ℂ c i : c)‖ = 1 := (stdOrthonormalBasis ℂ c).orthonormal.1 i
  intro hzero
  rw [Submodule.coe_eq_zero] at hzero
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

theorem cellLines_sSup (c : Submodule ℂ (H n)) :
    sSup ((cellLines c : Finset (Submodule ℂ (H n))) : Set (Submodule ℂ (H n))) = c := by
  set b := stdOrthonormalBasis ℂ c with hb_def
  show sSup ((Finset.univ.image (fun i => ℂ ∙ ((b i : c) : H n))) : Set (Submodule ℂ (H n))) = c
  have himg : ((Finset.univ.image (fun i => ℂ ∙ ((b i : c) : H n))) : Set (Submodule ℂ (H n)))
      = Set.range (fun i => ℂ ∙ ((b i : c) : H n)) := by
    ext x; simp [Set.mem_range]
  rw [himg, sSup_range]
  have hgeneric : (⨆ i, (Submodule.span ℂ ({((b i : c) : H n)} : Set (H n))))
      = Submodule.span ℂ (Set.range (fun i => ((b i : c) : H n))) := by
    apply le_antisymm
    · exact iSup_le (fun i => Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨i, rfl⟩))
    · rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      exact (le_iSup (fun i => Submodule.span ℂ ({((b i : c) : H n)} : Set (H n))) i)
        (Submodule.mem_span_singleton_self _)
  rw [hgeneric]
  have hspan_top : Submodule.span ℂ (Set.range (b.toBasis : Fin (Module.finrank ℂ c) → c)) = ⊤ :=
    b.toBasis.span_eq
  have hmapped := congrArg (Submodule.map c.subtype) hspan_top
  rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at hmapped
  convert hmapped using 2
  ext i
  simp [Function.comp]

theorem cellLines_ortho_within (c : Submodule ℂ (H n)) :
    ∀ x ∈ cellLines c, ∀ y ∈ cellLines c, x ≠ y → x ≤ yᗮ := by
  intro x hx y hy hxy
  simp only [cellLines, Finset.mem_image, Finset.mem_univ, true_and] at hx hy
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  have hij : i ≠ j := fun h => hxy (by rw [h])
  set e := stdOrthonormalBasis ℂ c with he_def
  have horth_c : (⟪e j, e i⟫_ℂ : ℂ) = 0 := e.orthonormal.2 (Ne.symm hij)
  have horth_V : (⟪((e j : c) : H n), ((e i : c) : H n)⟫_ℂ : ℂ) = 0 := by
    rw [← Submodule.coe_inner]
    exact horth_c
  rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_orthogonal]
  intro u hu
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hu
  rw [inner_smul_left, horth_V, mul_zero]

theorem cellLines_injective (c : Submodule ℂ (H n)) :
    Set.InjOn (fun i => (ℂ ∙ ((stdOrthonormalBasis ℂ c i : c) : H n) : Submodule ℂ (H n)))
      (↑(Finset.univ : Finset (Fin (Module.finrank ℂ c))) : Set (Fin (Module.finrank ℂ c))) := by
  intro i _ j _ heq
  by_contra hij
  set b := stdOrthonormalBasis ℂ c with hb_def
  have hbi_ne : ((b i : c) : H n) ≠ 0 := by
    have hnorm : ‖(b i : c)‖ = 1 := b.orthonormal.1 i
    intro hzero
    rw [Submodule.coe_eq_zero] at hzero
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  have heq' : (ℂ ∙ ((b i : c) : H n)) = (ℂ ∙ ((b j : c) : H n)) := heq
  have hbi_mem : ((b i : c) : H n) ∈ (ℂ ∙ ((b j : c) : H n)) :=
    heq' ▸ Submodule.mem_span_singleton_self _
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hbi_mem
  have hbjbj_c : (⟪b j, b j⟫_ℂ : ℂ) = 1 := by
    have hn : ‖(b j : c)‖ = 1 := b.orthonormal.1 j
    have heq2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (b j)
    rw [heq2, hn]; norm_num
  have hbjbj : (⟪((b j : c) : H n), ((b j : c) : H n)⟫_ℂ : ℂ) = 1 := by
    rw [← Submodule.coe_inner]; exact hbjbj_c
  have horth : (⟪((b j : c) : H n), ((b i : c) : H n)⟫_ℂ : ℂ) = 0 := by
    have h1 : (⟪b i, b j⟫_ℂ : ℂ) = 0 := b.orthonormal.2 hij
    have h1' : (⟪((b i : c) : H n), ((b j : c) : H n)⟫_ℂ : ℂ) = 0 := by
      rw [← Submodule.coe_inner]; exact h1
    have h2 : (⟪((b j : c) : H n), ((b i : c) : H n)⟫_ℂ : ℂ)
        = starRingEnd ℂ ⟪((b i : c) : H n), ((b j : c) : H n)⟫_ℂ :=
      (inner_conj_symm ((b j : c) : H n) ((b i : c) : H n)).symm
    rw [h2, h1']
    simp
  rw [← hd, inner_smul_right, hbjbj, mul_one] at horth
  exact hbi_ne (by rw [← hd, horth, zero_smul])

theorem cellLines_sum_eq (c : Submodule ℂ (H n)) (F : Submodule ℂ (H n) → ℝ) :
    ∑ x ∈ cellLines c, F x
    = ∑ i : Fin (Module.finrank ℂ c), F (ℂ ∙ ((stdOrthonormalBasis ℂ c i : c) : H n)) := by
  unfold cellLines
  rw [Finset.sum_image (cellLines_injective c)]

/-- The full refinement of an arbitrary perspective `D`: glue, across
    every cell of `D`, an orthonormal basis proper to that cell. -/
noncomputable def refinePerspective (D : Perspective n) : Perspective n where
  cells := D.cells.biUnion cellLines
  nz := by
    intro x hx
    simp only [Finset.mem_biUnion] at hx
    obtain ⟨c, hc, hx'⟩ := hx
    exact cellLines_ne_bot c x hx'
  ortho := by
    intro x hx y hy hxy
    simp only [Finset.mem_biUnion] at hx hy
    obtain ⟨c, hc, hx'⟩ := hx
    obtain ⟨c', hc', hy'⟩ := hy
    by_cases hcc : c = c'
    · subst hcc
      exact cellLines_ortho_within c x hx' y hy' hxy
    · have hxc : x ≤ c := cellLines_le c x hx'
      have hyc' : y ≤ c' := cellLines_le c' y hy'
      have h1 : c ≤ c'ᗮ := D.ortho c hc c' hc' hcc
      have h2 : c'ᗮ ≤ yᗮ := Submodule.orthogonal_le hyc'
      exact hxc.trans (h1.trans h2)
  span := by
    show sSup ((D.cells.biUnion cellLines : Finset (Submodule ℂ (H n))) : Set (Submodule ℂ (H n))) = ⊤
    apply le_antisymm le_top
    rw [← D.span]
    apply sSup_le
    intro c hc
    simp only [Finset.mem_coe] at hc
    rw [← cellLines_sSup c]
    apply sSup_le_sSup
    intro x hx
    simp only [Finset.coe_biUnion, Set.mem_iUnion]
    exact ⟨c, hc, hx⟩

theorem refinePerspective_refines (D : Perspective n) : Refines (refinePerspective D) D := by
  intro x hx
  simp only [refinePerspective, Finset.mem_biUnion] at hx
  obtain ⟨c, hc, hx'⟩ := hx
  exact ⟨c, hc, cellLines_le c x hx'⟩

/-- The (Grain) filter of `refinePerspective D` at a cell `c` of `D`
    coincides exactly with `cellLines c`. -/
theorem refine_filter_eq_cellLines (D : Perspective n) (c : Submodule ℂ (H n)) (hc : c ∈ D.cells) :
    (refinePerspective D).cells.filter (· ≤ c) = cellLines c := by
  ext x
  simp only [Finset.mem_filter, refinePerspective, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨c', hc', hx'⟩, hxc⟩
    by_cases hcc : c' = c
    · rwa [hcc] at hx'
    · exfalso
      have hxc' : x ≤ c' := cellLines_le c' x hx'
      have hxne : x ≠ ⊥ := cellLines_ne_bot c' x hx'
      have h1 : c' ≤ cᗮ := D.ortho c' hc' c hc hcc
      have h2 : x ≤ cᗮ := hxc'.trans h1
      apply hxne
      rw [Submodule.eq_bot_iff]
      intro y hy
      have hy1 : y ∈ c := hxc hy
      have hy2 : y ∈ cᗮ := h2 hy
      have hzero : (⟪y, y⟫_ℂ : ℂ) = 0 := (Submodule.mem_orthogonal c y).mp hy2 y hy1
      exact inner_self_eq_zero.mp hzero
  · intro hx'
    exact ⟨⟨c, hc, hx'⟩, cellLines_le c x hx'⟩

end
end QuantumFoundations.BornRule
