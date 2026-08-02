import QuantumFoundations.Naimark.BinaryImpl.Defs

/-!
**FR.** # Ancilla répliquée : un agrandissement qui ne change PAS le ratio de rang

Pour toute implémentation `I : BinaryImpl n E ι` et tout `a₀ : Fin a`
(`a ≥ 1`), `replicatedAncillaImpl I a₀` place `I` dans le bloc `a₀` d'un
espace ambiant `a` fois plus grand `EuclideanSpace ℂ (Fin a × ι)`, les
`a` blocs étant des copies orthogonales identiques préparées par
`blockSingle`/`blockCoord`. C'est la forme la plus simple d'"ajout
d'ancilla" : elle NE MODIFIE PAS l'effet réalisé (`realizes` reste `E`),
et son seul effet global est de multiplier `ambientDim` ET `projectorRank`
par le même facteur `a` (`replicatedAncilla_ambientDim`,
`replicatedAncilla_projectorRank`). Le RATIO `rankRatio I :=
projectorRank I / ambientDim I` (ℚ) est donc EXACTEMENT invariant sous
réplication d'ancilla (`rankRatio_replicatedAncilla`), quel que soit `a`.

Combiné à `StrictIso.rankRatio_eq` (un isomorphisme strict force l'égalité
des ratios, car il force séparément l'égalité de `ambientDim` et de
`projectorRank`, `Defs.lean`), ceci fournit un invariant NUMÉRIQUE simple
et calculable qui survit à toute réplication d'ancilla -- l'outil dont se
sert `TernaryFusion.lean` pour montrer qu'aucune réplication, aussi grande
soit-elle, ne peut rendre isomorphes deux implémentations dont les ratios
`1/2` et `1/3` diffèrent nativement.

**Choix technique.** `blockSingle ι a₀`/`blockCoord ι a₀` encodent/lisent
le bloc `a₀` d'un espace produit `EuclideanSpace ℂ (α × ι)` par un
`if`-`then`-`else` explicite sur les coordonnées, ce qui permet de
calculer `adjoint`/`inner` sans jamais passer par une isométrie de
sous-espace typée `Submodule ℂ (EuclideanSpace ℂ ι)` (le diamant
d'instances documenté dans `MinimalUniqueness.lean`). Le calcul du rang de
`replicateOperator A := ∑ a, blockSingle a ∘ A ∘ blockCoord a` route par
`blockAssemble` (assemblage explicite d'une famille indexée par `α`) et
l'égalité ensembliste `range (replicateOperator A) = range (blockAssemble
∘ (range A).subtype.compLeft α)`, dont le second membre a pour rang
`Fintype.card α * finrank (range A)` par injectivité de la composée et
`Module.finrank_pi_fintype`.

**EN.** # Replicated ancilla: an enlargement that does NOT change the rank ratio

For any implementation `I : BinaryImpl n E ι` and any `a₀ : Fin a`
(`a ≥ 1`), `replicatedAncillaImpl I a₀` places `I` in block `a₀` of an
ambient space `a` times larger, `EuclideanSpace ℂ (Fin a × ι)`, the `a`
blocks being identical orthogonal copies prepared by
`blockSingle`/`blockCoord`. This is the simplest form of "ancilla
addition": it does NOT change the realized effect (`realizes` stays `E`),
and its only global effect is to multiply both `ambientDim` AND
`projectorRank` by the same factor `a` (`replicatedAncilla_ambientDim`,
`replicatedAncilla_projectorRank`). The RATIO `rankRatio I :=
projectorRank I / ambientDim I` (ℚ) is therefore EXACTLY invariant under
ancilla replication (`rankRatio_replicatedAncilla`), for every `a`.

Combined with `StrictIso.rankRatio_eq` (a strict isomorphism forces equal
ratios, since it separately forces equal `ambientDim` and equal
`projectorRank`, `Defs.lean`), this yields a simple computable NUMERIC
invariant that survives any ancilla replication -- the tool
`TernaryFusion.lean` uses to show that no replication, however large, can
make isomorphic two implementations whose ratios `1/2` and `1/3` natively
differ.

**Technical choice.** `blockSingle ι a₀`/`blockCoord ι a₀` encode/read
block `a₀` of a product space `EuclideanSpace ℂ (α × ι)` via an explicit
`if`-`then`-`else` on coordinates, which allows computing `adjoint`/`inner`
without ever going through a submodule-typed isometry `Submodule ℂ
(EuclideanSpace ℂ ι)` (the instance diamond documented in
`MinimalUniqueness.lean`). The rank computation for `replicateOperator A
:= ∑ a, blockSingle a ∘ A ∘ blockCoord a` routes through `blockAssemble`
(explicit assembly of an `α`-indexed family) and the set equality `range
(replicateOperator A) = range (blockAssemble ∘ (range A).subtype.compLeft
α)`, whose right-hand side has rank `Fintype.card α * finrank (range A)`
by injectivity of the composite and `Module.finrank_pi_fintype`.
-/

namespace QuantumFoundations.Naimark.BinaryImpl

open QuantumFoundations Gleason
open scoped InnerProductSpace

noncomputable section

/-- Injects `EuclideanSpace ℂ ι` into block `a₀` of the `α`-indexed product
`EuclideanSpace ℂ (α × ι)`, zero elsewhere. -/
def blockSingle {α : Type} [Fintype α] [DecidableEq α] (ι : Type) [Fintype ι] (a₀ : α) :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ (α × ι) where
  toFun x := WithLp.toLp 2 (fun p : α × ι => if p.1 = a₀ then x p.2 else 0)
  map_add' x y := by
    rw [← WithLp.toLp_add]; congr 1; funext p; by_cases h : p.1 = a₀ <;> simp [h]
  map_smul' c x := by
    rw [← WithLp.toLp_smul]; congr 1; funext p; by_cases h : p.1 = a₀ <;> simp [h]

/-- Reads out block `a₀` of the `α`-indexed product `EuclideanSpace ℂ (α × ι)`. -/
def blockCoord {α : Type} [Fintype α] [DecidableEq α] (ι : Type) [Fintype ι] (a₀ : α) :
    EuclideanSpace ℂ (α × ι) →ₗ[ℂ] EuclideanSpace ℂ ι where
  toFun w := WithLp.toLp 2 (fun k : ι => w (a₀, k))
  map_add' w w' := by rw [← WithLp.toLp_add]; congr 1
  map_smul' c w := by rw [← WithLp.toLp_smul]; congr 1

theorem inner_blockSingle {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] (a₀ : α)
    (x : EuclideanSpace ℂ ι) (w : EuclideanSpace ℂ (α × ι)) :
    ⟪blockSingle ι a₀ x, w⟫_ℂ = ⟪x, blockCoord ι a₀ w⟫_ℂ := by
  show ⟪(WithLp.toLp 2 (fun p : α × ι => if p.1 = a₀ then x p.2 else 0) : EuclideanSpace ℂ (α × ι)),
    w⟫_ℂ = _
  rw [PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_eq_single a₀]
  · simp [blockCoord]
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro k _
    simp [hb]
  · intro h; exact absurd (Finset.mem_univ a₀) h

/-- `blockSingle` and `blockCoord` are mutually adjoint. -/
theorem adjoint_blockSingle {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι]
    (a₀ : α) : LinearMap.adjoint (blockSingle ι a₀) = blockCoord ι a₀ := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  rw [← inner_conj_symm (blockCoord ι a₀ x) y, ← inner_blockSingle a₀ y x,
    inner_conj_symm x (blockSingle ι a₀ y)]

theorem adjoint_blockCoord {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι]
    (a₀ : α) : LinearMap.adjoint (blockCoord ι a₀) = blockSingle ι a₀ := by
  rw [← adjoint_blockSingle a₀, LinearMap.adjoint_adjoint]

/-- Reading block `a` after writing block `a'` collapses to the identity
when `a = a'`, and to zero otherwise. -/
theorem blockCoord_blockSingle {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι]
    (a a' : α) :
    blockCoord ι a ∘ₗ blockSingle ι a' = if a = a' then LinearMap.id else 0 := by
  by_cases h : a = a'
  · subst h
    simp only [if_true]
    apply LinearMap.ext
    intro x
    show WithLp.toLp 2 (fun k : ι => (blockSingle ι a x) (a, k)) = x
    simp only [blockSingle, LinearMap.coe_mk, AddHom.coe_mk]
    exact WithLp.toLp_ofLp (p := 2) x
  · simp only [if_neg h]
    apply LinearMap.ext
    intro x
    show WithLp.toLp 2 (fun k : ι => (blockSingle ι a' x) (a, k)) = (0 : EuclideanSpace ℂ ι)
    simp only [blockSingle, LinearMap.coe_mk, AddHom.coe_mk, if_neg h]
    rfl

/-- The block-diagonal operator applying `A` identically to each of the
`α` blocks of `EuclideanSpace ℂ (α × ι)`. -/
def replicateOperator {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι]
    (A : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ (α × ι) →ₗ[ℂ] EuclideanSpace ℂ (α × ι) :=
  ∑ a : α, blockSingle ι a ∘ₗ A ∘ₗ blockCoord ι a

theorem blockCoord_replicateOperator {α : Type} [Fintype α] [DecidableEq α] {ι : Type}
    [Fintype ι] (A : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (a₀ : α)
    (w : EuclideanSpace ℂ (α × ι)) :
    blockCoord ι a₀ (replicateOperator A w) = A (blockCoord ι a₀ w) := by
  show (blockCoord ι a₀ ∘ₗ (∑ a : α, blockSingle ι a ∘ₗ A ∘ₗ blockCoord ι a)) w
    = A (blockCoord ι a₀ w)
  rw [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  have step : ∀ a : α, blockCoord ι a₀ ((blockSingle ι a ∘ₗ A ∘ₗ blockCoord ι a) w)
      = if a₀ = a then A (blockCoord ι a₀ w) else 0 := by
    intro a
    show blockCoord ι a₀ (blockSingle ι a (A (blockCoord ι a w))) = _
    have h := LinearMap.congr_fun (blockCoord_blockSingle (ι := ι) a₀ a) (A (blockCoord ι a w))
    simp only [LinearMap.comp_apply] at h
    by_cases hcase : a₀ = a
    · subst hcase; simpa using h
    · simp only [if_neg hcase] at h
      rw [h]
      simp [hcase]
  simp only [step]
  rw [Finset.sum_ite_eq Finset.univ a₀ (fun _ => A (blockCoord ι a₀ w)), if_pos (Finset.mem_univ a₀)]

theorem replicateOperator_apply {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι]
    (A : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (w : EuclideanSpace ℂ (α × ι)) :
    replicateOperator A w = ∑ a : α, blockSingle ι a (A (blockCoord ι a w)) := by
  show (∑ a : α, blockSingle ι a ∘ₗ A ∘ₗ blockCoord ι a) w = _
  rw [LinearMap.sum_apply]
  rfl

/-- Assembles a family of per-block vectors into a single ambient vector. -/
def blockAssemble {α : Type} [Fintype α] [DecidableEq α] (ι : Type) [Fintype ι] :
    (α → EuclideanSpace ℂ ι) →ₗ[ℂ] EuclideanSpace ℂ (α × ι) where
  toFun v := ∑ a : α, blockSingle ι a (v a)
  map_add' v v' := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← map_add]
    rfl
  map_smul' c v := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [← map_smul]
    rfl

theorem blockCoord_blockAssemble {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι]
    (v : α → EuclideanSpace ℂ ι) (a₀ : α) :
    blockCoord ι a₀ (blockAssemble ι v) = v a₀ := by
  show blockCoord ι a₀ (∑ a : α, blockSingle ι a (v a)) = v a₀
  rw [map_sum]
  have step : ∀ a : α, blockCoord ι a₀ (blockSingle ι a (v a)) = if a₀ = a then v a₀ else 0 := by
    intro a
    have h := LinearMap.congr_fun (blockCoord_blockSingle (ι := ι) a₀ a) (v a)
    simp only [LinearMap.comp_apply] at h
    by_cases hcase : a₀ = a
    · subst hcase; simpa using h
    · simp only [if_neg hcase] at h; rw [h]; simp [hcase]
  simp only [step]
  rw [Finset.sum_ite_eq Finset.univ a₀ (fun _ => v a₀), if_pos (Finset.mem_univ a₀)]

theorem blockAssemble_injective {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] :
    Function.Injective (blockAssemble (α := α) ι) := by
  rw [← LinearMap.ker_eq_bot]
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  funext a
  have h := blockCoord_blockAssemble v a
  rw [hv, map_zero] at h
  exact h.symm

theorem replicateOperator_eq_blockAssemble_comp {α : Type} [Fintype α] [DecidableEq α]
    {ι : Type} [Fintype ι] (A : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (w : EuclideanSpace ℂ (α × ι)) :
    replicateOperator A w = blockAssemble ι (fun a => A (blockCoord ι a w)) := by
  rw [replicateOperator_apply]
  rfl

/-- A vector in the range of an idempotent operator is a fixed point. -/
theorem fixed_of_mem_range_idempotent {ι : Type} [Fintype ι]
    {A : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι} (hA : A ∘ₗ A = A)
    {y : EuclideanSpace ℂ ι} (hy : y ∈ LinearMap.range A) : A y = y := by
  obtain ⟨x, rfl⟩ := hy
  exact LinearMap.congr_fun hA x

/-- The range of `replicateOperator A` (for `A` idempotent) is exactly the
range of the composite that assembles, per block, an arbitrary element of
`range A`. -/
theorem range_replicateOperator_eq {α : Type} [Fintype α] [DecidableEq α] {ι : Type}
    [Fintype ι] {A : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι} (hA : A ∘ₗ A = A) :
    LinearMap.range (replicateOperator (α := α) A)
      = LinearMap.range (blockAssemble ι ∘ₗ (LinearMap.range A).subtype.compLeft α) := by
  apply Submodule.ext
  intro y
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨fun a => ⟨A (blockCoord ι a w), ⟨blockCoord ι a w, rfl⟩⟩, ?_⟩
    rw [replicateOperator_eq_blockAssemble_comp]
    rfl
  · rintro ⟨f, rfl⟩
    refine ⟨blockAssemble ι (fun a => (f a : EuclideanSpace ℂ ι)), ?_⟩
    rw [replicateOperator_eq_blockAssemble_comp]
    have hcomp : (blockAssemble ι ∘ₗ (LinearMap.range A).subtype.compLeft α) f
        = blockAssemble ι (fun a => (f a : EuclideanSpace ℂ ι)) := by
      rw [LinearMap.comp_apply]
      congr 1
    rw [hcomp]
    congr 1
    funext a
    rw [blockCoord_blockAssemble]
    exact fixed_of_mem_range_idempotent hA (f a).2

/-- The rank of a block-replicated idempotent scales exactly by the
number of blocks. -/
theorem finrank_range_replicateOperator (α : Type) [Fintype α] [DecidableEq α] {ι : Type}
    [Fintype ι] {A : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι} (hA : A ∘ₗ A = A) :
    Module.finrank ℂ (LinearMap.range (replicateOperator (α := α) A))
      = Fintype.card α * Module.finrank ℂ (LinearMap.range A) := by
  rw [range_replicateOperator_eq (α := α) hA]
  have hinj : Function.Injective (blockAssemble ι ∘ₗ
      (LinearMap.range A).subtype.compLeft α) := by
    apply Function.Injective.comp blockAssemble_injective
    intro f g hfg
    funext a
    have h := congr_fun hfg a
    simp only [LinearMap.compLeft_apply] at h
    exact Subtype.ext h
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_pi_fintype ℂ]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

end

noncomputable section resolution

theorem replicateOperator_idempotent (α : Type) [Fintype α] [DecidableEq α] {ι : Type}
    [Fintype ι] {A : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι} (hA : A ∘ₗ A = A) :
    replicateOperator (α := α) A ∘ₗ replicateOperator A = replicateOperator A := by
  apply LinearMap.ext
  intro w
  show replicateOperator A (replicateOperator A w) = replicateOperator A w
  have hstep : ∀ v : EuclideanSpace ℂ (α × ι), replicateOperator A v
      = ∑ a : α, blockSingle ι a (A (blockCoord ι a v)) := by
    intro v
    show (∑ a : α, blockSingle ι a ∘ₗ A ∘ₗ blockCoord ι a) v = _
    rw [LinearMap.sum_apply]
    rfl
  rw [hstep (replicateOperator A w)]
  conv_rhs => rw [hstep w]
  apply Finset.sum_congr rfl
  intro a _
  rw [blockCoord_replicateOperator]
  congr 1
  exact LinearMap.congr_fun hA (blockCoord ι a w)

theorem adjoint_replicateOperator (α : Type) [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι]
    (A : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) :
    LinearMap.adjoint (replicateOperator (α := α) A) = replicateOperator (LinearMap.adjoint A) := by
  show LinearMap.adjoint (∑ a : α, blockSingle ι a ∘ₗ A ∘ₗ blockCoord ι a) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp, adjoint_blockSingle, adjoint_blockCoord,
    LinearMap.comp_assoc]

theorem replicateOperator_symmetric (α : Type) [Fintype α] [DecidableEq α] {ι : Type}
    [Fintype ι] {A : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι} (hA : LinearMap.IsSymmetric A) :
    LinearMap.IsSymmetric (replicateOperator (α := α) A) := by
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
  show LinearMap.adjoint (replicateOperator (α := α) A) = replicateOperator A
  rw [adjoint_replicateOperator, hA.adjoint_eq]

end resolution

noncomputable section ancilla

variable {n : ℕ} {E : H n →ₗ[ℂ] H n} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `I` placed in block `a₀` of an ambient space enlarged `a`-fold by an
identical replica of `I` in every other block. -/
def replicatedAncillaImpl {a : ℕ} (I : BinaryImpl n E ι) (a₀ : Fin a) :
    BinaryImpl n E (Fin a × ι) where
  encoding := blockSingle ι a₀ ∘ₗ I.encoding
  cell := replicateOperator I.cell
  encoding_isometry := by
    apply LinearMap.ext
    intro x
    show LinearMap.adjoint (blockSingle ι a₀ ∘ₗ I.encoding) (blockSingle ι a₀ (I.encoding x)) = x
    have hadj : LinearMap.adjoint (blockSingle ι a₀ ∘ₗ I.encoding)
        = LinearMap.adjoint I.encoding ∘ₗ blockCoord ι a₀ := by
      rw [LinearMap.adjoint_comp, adjoint_blockSingle]
    rw [hadj]
    show LinearMap.adjoint I.encoding (blockCoord ι a₀ (blockSingle ι a₀ (I.encoding x))) = x
    have h := LinearMap.congr_fun (blockCoord_blockSingle (ι := ι) a₀ a₀) (I.encoding x)
    simp only [LinearMap.comp_apply] at h
    rw [h]
    have h2 := LinearMap.congr_fun I.encoding_isometry x
    simpa using h2
  cell_isProjection := ⟨replicateOperator_idempotent (Fin a) I.cell_idempotent,
    replicateOperator_symmetric (Fin a) I.cell_symmetric⟩
  realizes := by
    apply LinearMap.ext
    intro x
    show LinearMap.adjoint (blockSingle ι a₀ ∘ₗ I.encoding)
      (replicateOperator I.cell (blockSingle ι a₀ (I.encoding x))) = E x
    have hadj : LinearMap.adjoint (blockSingle ι a₀ ∘ₗ I.encoding)
        = LinearMap.adjoint I.encoding ∘ₗ blockCoord ι a₀ := by
      rw [LinearMap.adjoint_comp, adjoint_blockSingle]
    rw [hadj]
    show LinearMap.adjoint I.encoding
      (blockCoord ι a₀ (replicateOperator I.cell (blockSingle ι a₀ (I.encoding x)))) = E x
    rw [blockCoord_replicateOperator]
    have h := LinearMap.congr_fun (blockCoord_blockSingle (ι := ι) a₀ a₀) (I.encoding x)
    simp only [LinearMap.comp_apply] at h
    rw [h]
    have h2 := LinearMap.congr_fun I.realizes x
    simpa using h2

theorem replicatedAncilla_ambientDim {a : ℕ} (I : BinaryImpl n E ι) (a₀ : Fin a) :
    (replicatedAncillaImpl I a₀).ambientDim = a * I.ambientDim := by
  show Fintype.card (Fin a × ι) = a * Fintype.card ι
  rw [Fintype.card_prod, Fintype.card_fin]

theorem replicatedAncilla_projectorRank {a : ℕ} (I : BinaryImpl n E ι) (a₀ : Fin a) :
    (replicatedAncillaImpl I a₀).projectorRank = a * I.projectorRank := by
  show Module.finrank ℂ (LinearMap.range (replicateOperator I.cell)) = a * I.projectorRank
  rw [finrank_range_replicateOperator (Fin a) I.cell_idempotent, Fintype.card_fin]
  rfl

/-- The rank ratio of an implementation: the fraction of the ambient space
occupied by the event sector. Deliberately valued in `ℚ`, not `ℝ` or a
probability, since only its EXACT equality under `StrictIso` and its
invariance under ancilla replication are used. -/
def rankRatio (I : BinaryImpl n E ι) : ℚ := (I.projectorRank : ℚ) / (I.ambientDim : ℚ)

/-- Replicating the ancilla leaves `rankRatio` exactly unchanged. -/
theorem rankRatio_replicatedAncilla {a : ℕ} (I : BinaryImpl n E ι) (a₀ : Fin a) :
    rankRatio (replicatedAncillaImpl I a₀) = rankRatio I := by
  show ((replicatedAncillaImpl I a₀).projectorRank : ℚ)
      / ((replicatedAncillaImpl I a₀).ambientDim : ℚ)
    = (I.projectorRank : ℚ) / (I.ambientDim : ℚ)
  rw [replicatedAncilla_projectorRank, replicatedAncilla_ambientDim]
  have ha : (a : ℚ) ≠ 0 := by
    have : (0 : ℕ) < a := a₀.pos
    exact_mod_cast this.ne'
  push_cast
  rw [mul_div_mul_left _ _ ha]

/-- A strict isomorphism forces equal `rankRatio` (it forces equal
`ambientDim` and equal `projectorRank` separately). -/
theorem StrictIso.rankRatio_eq {κ : Type} [Fintype κ] [DecidableEq κ]
    {I : BinaryImpl n E ι} {J : BinaryImpl n E κ} (h : BinaryImpl.StrictIso I J) :
    rankRatio I = rankRatio J := by
  have hr : I.projectorRank = J.projectorRank := h.projectorRange_finrank_eq
  have hd : I.ambientDim = J.ambientDim := h.ambientDim_eq
  show (I.projectorRank : ℚ) / (I.ambientDim : ℚ) = (J.projectorRank : ℚ) / (J.ambientDim : ℚ)
  rw [hr, hd]

end ancilla

end QuantumFoundations.Naimark.BinaryImpl
