import QuantumFoundations.Uhlhorn.Defs
import Gleason.Complex.RealSections

/-!
**FR.** # U3a — Extension d'une fonction-cadre sur les droites en `ProjMeasure` complet

Pièce à part entière, PAS un détail interne de U3b (`GleasonTwice.lean`) : pour
appliquer `Gleason.gleason`, qui prend un `ProjMeasure` complet (défini et additif
sur TOUT sous-espace, cf. `Gleason.Defs`), à la fonction-cadre
`φ_D(P) := tr(D · φ(P))` de la preuve de Šemrl (qui n'est a priori définie que sur
les droites `Proj1 n`), il faut d'abord l'étendre.

**Confirmé par audit du dépôt `gleason` (Étape 0 de U0)** : aucun lemme de ce type
n'existe dans `gleason-theorem-lean`. Les deux seuls sites de construction d'un
`ProjMeasure` du dépôt (`EffectMeasure.toProjMeasure`, `pureState`) donnent tous
deux une formule FERMÉE valable directement sur tout sous-espace, sans jamais
étendre une donnée partielle définie seulement sur les droites. Décision : ce
lemme reste dans `quantum-foundations-lean` (namespace `Uhlhorn`), pas dans
`gleason-theorem-lean` — même s'il s'agit d'un fait Gleason générique, on ne
rouvre pas le dépôt public tagué pour ce besoin.

**Écart majeur par rapport à la stratégie de reconnaissance initiale** : le point
délicat anticipé (indépendance du choix de base orthonormée, Sous-lemme 1) N'A PAS
été redémontré depuis zéro par concaténation de bases (`Fin k ⊕ Fin l` → `Fin n`
via `finSumFinEquiv`/`Fin.append`). `Gleason.Complex.RealSections` contient déjà,
en interne, EXACTEMENT cet argument sous forme vectorielle :
`Gleason.cframe_sum_invariant` (pour une fonction-cadre `g : H n → ℝ` satisfaisant
`IsCFrameFunction g W`, deux familles orthonormées de même taille engendrant le
même sous-espace donnent la même somme). La stratégie retenue ici pont `Proj1 n`
vers cette machinerie déjà prouvée (`gv : H n → ℝ`, la version vectorielle de `g`,
`isCFrameFunction_gv` montrant `gv` satisfait `IsCFrameFunction`) plutôt que de
refaire la construction indépendamment — le seul travail de concaténation de
bases nécessaire ici reste `Sous-lemme 5` (`add_isOrtho`, via `Sum.elim`), sur un
sous-ensemble bien plus restreint du problème (juste `A` et `B`, pas la
construction générale de l'extension elle-même).

**EN.** # U3a — Extending a frame function on lines to a full ProjMeasure

A component in its own right, NOT an internal detail of U3b
(GleasonTwice.lean): to apply Gleason.gleason, which takes a full
ProjMeasure defined and additive on EVERY subspace (see Gleason.Defs), to
the frame function φ_D(P) := tr(D · φ(P)) in Šemrl's proof, which is a priori
defined only on the lines Proj1 n, the function must first be extended.

Confirmed by auditing the gleason repository (Step 0 of U0): no lemma of
this form exists in gleason-theorem-lean. The only two construction sites
for a ProjMeasure in that repository (EffectMeasure.toProjMeasure,
pureState) both provide a CLOSED formula valid directly on every subspace,
and never extend partial data defined only on lines. Decision: this lemma
remains in quantum-foundations-lean (namespace Uhlhorn), not in
gleason-theorem-lean. Although it is a generic Gleason fact, the tagged
public repository is not reopened for this need.

Major deviation from the initial reconnaissance strategy: the anticipated
delicate point, independence from the choice of orthonormal basis
(Sublemma 1), was not reproved from first principles by concatenating bases
(Fin k ⊕ Fin l → Fin n through finSumFinEquiv/Fin.append).
Internally, Gleason.Complex.RealSections already contains exactly this
argument in vector form: Gleason.cframe_sum_invariant (for a frame function
g : H n → ℝ satisfying IsCFrameFunction g W, two orthonormal families of
the same size spanning the same subspace have equal sums). The strategy
adopted here bridges Proj1 n to this already-proved machinery
(gv : H n → ℝ, the vector version of g, with isCFrameFunction_gv
showing that gv satisfies IsCFrameFunction) rather than rebuilding the
construction independently. The only basis-concatenation work still needed
here is Sous-lemme 5 (add_isOrtho, via Sum.elim), for a much narrower part
of the problem—only A and B, rather than the general construction of the
extension itself.
-/

namespace QuantumFoundations.Uhlhorn

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ}

/--
**FR.** Version vectorielle de `g`, valeur poubelle `0` hors de la sphère unité.

**EN.** Vector version of g, with junk value 0 outside the unit sphere.
-/
private noncomputable def gv (g : Proj1 n → ℝ) : H n → ℝ :=
  fun x => if h : ‖x‖ = 1 then g (Proj1.mk_unit x h) else 0

private theorem gv_of_norm_one {g : Proj1 n → ℝ} {x : H n} (hx : ‖x‖ = 1) :
    gv g x = g (Proj1.mk_unit x hx) := dif_pos hx

/--
**FR.** `gv g` est une fonction-cadre complexe de poids `1`, au sens de
`Gleason.IsCFrameFunction` — pont vers `Gleason.cframe_sum_invariant`.

**EN.** gv g is a complex frame function of weight 1 in the sense of
Gleason.IsCFrameFunction, providing the bridge to
Gleason.cframe_sum_invariant.
-/
private theorem isCFrameFunction_gv {g : Proj1 n → ℝ} (hg : IsFrameFunctionOnLines g) :
    IsCFrameFunction (gv g) 1 := by
  intro b
  rw [Finset.sum_congr rfl (fun i _ => gv_of_norm_one (b.norm_eq_one i))]
  exact hg.2 b

private theorem gv_nonneg {g : Proj1 n → ℝ} (hg : IsFrameFunctionOnLines g) (x : H n) :
    0 ≤ gv g x := by
  unfold gv
  split
  · exact hg.1 _
  · exact le_refl 0

private theorem orthonormal_stdBasis_coe (A : Submodule ℂ (H n)) :
    Orthonormal ℂ (fun i => ((stdOrthonormalBasis ℂ A) i : H n)) :=
  show Orthonormal ℂ (⇑(A.subtypeₗᵢ) ∘ ⇑(stdOrthonormalBasis ℂ A)) from
    (LinearIsometry.orthonormal_comp_iff (A.subtypeₗᵢ)).mpr (stdOrthonormalBasis ℂ A).orthonormal

private theorem span_stdBasis_coe (A : Submodule ℂ (H n)) :
    Submodule.span ℂ (Set.range (fun i => ((stdOrthonormalBasis ℂ A) i : H n))) = A := by
  have h1 : Set.range (fun i => ((stdOrthonormalBasis ℂ A) i : H n))
      = (Submodule.subtype A) '' (Set.range (stdOrthonormalBasis ℂ A)) := by
    rw [← Set.range_comp]; rfl
  rw [h1, ← LinearMap.map_span, ← OrthonormalBasis.coe_toBasis,
    (stdOrthonormalBasis ℂ A).toBasis.span_eq, Submodule.map_subtype_top]

/--
**FR.** Somme cadre sur la base orthonormée standard de `A` (`stdOrthonormalBasis`).

**EN.** Frame sum over the standard orthonormal basis of A
(stdOrthonormalBasis).
-/
private noncomputable def frameSum (g : Proj1 n → ℝ) (A : Submodule ℂ (H n)) : ℝ :=
  ∑ i, gv g ((stdOrthonormalBasis ℂ A) i : H n)

/--
**FR.** **Sous-lemme 1 (indépendance du choix de base)**, sous forme générique (tout
`Fintype ι` de bon cardinal, pas seulement `Fin (finrank A)`) : réutilise
directement `Gleason.cframe_sum_invariant`, déjà prouvé dans la dépendance
épinglée pour l'énoncé analogue sur les frame functions vectorielles.

**EN.** Sublemma 1 (independence from the choice of basis), in generic form
(for any Fintype ι of the correct cardinality, not only
Fin (finrank A)): directly reuses Gleason.cframe_sum_invariant, already
proved in the pinned dependency for the analogous statement about
vector-valued frame functions.
-/
private theorem frameSum_eq_sum_of_orthonormal_spanning {g : Proj1 n → ℝ}
    (hg : IsFrameFunctionOnLines g) {A : Submodule ℂ (H n)} {ι : Type*} [Fintype ι]
    (hcard : Fintype.card ι = Module.finrank ℂ A) (v : ι → H n) (hv : Orthonormal ℂ v)
    (hspan : Submodule.span ℂ (Set.range v) = A) :
    frameSum g A = ∑ i, gv g (v i) := by
  set e : ι ≃ Fin (Module.finrank ℂ A) := Fintype.equivFinOfCardEq hcard with he
  have hkn : Module.finrank ℂ A ≤ n := by
    calc Module.finrank ℂ A ≤ Module.finrank ℂ (H n) := Submodule.finrank_le A
      _ = n := by simp
  have hv' : Orthonormal ℂ (v ∘ e.symm) := hv.comp e.symm e.symm.injective
  have hspan' : Submodule.span ℂ (Set.range (v ∘ e.symm)) = A := by
    rw [EquivLike.range_comp]; exact hspan
  have hmain := cframe_sum_invariant (isCFrameFunction_gv hg) hkn
    (fun i => ((stdOrthonormalBasis ℂ A) i : H n)) (v ∘ e.symm)
    (orthonormal_stdBasis_coe A) hv' (by rw [span_stdBasis_coe A, hspan'])
  rw [frameSum, hmain]
  exact Equiv.sum_comp e.symm (fun j => gv g (v j))

/-- **Sous-lemme 3** (`top_eq_one`). -/
private theorem frameSum_top {g : Proj1 n → ℝ} (hg : IsFrameFunctionOnLines g) :
    frameSum g (⊤ : Submodule ℂ (H n)) = 1 := by
  set b : OrthonormalBasis (Fin n) ℂ (H n) := EuclideanSpace.basisFun (Fin n) ℂ with hb
  have hcard : Fintype.card (Fin n) = Module.finrank ℂ (⊤ : Submodule ℂ (H n)) := by
    rw [finrank_top]; simp
  rw [frameSum_eq_sum_of_orthonormal_spanning hg hcard b b.orthonormal b.toBasis.span_eq]
  exact isCFrameFunction_gv hg b

/-- **Sous-lemme 4** (`nonneg`). -/
private theorem frameSum_nonneg {g : Proj1 n → ℝ} (hg : IsFrameFunctionOnLines g)
    (A : Submodule ℂ (H n)) : 0 ≤ frameSum g A :=
  Finset.sum_nonneg (fun _ _ => gv_nonneg hg _)

/--
**FR.** **Sous-lemme 5** (`add_isOrtho`) : seul point où une concaténation de bases
orthonormées est réellement construite à la main dans ce fichier (via `Sum.elim`,
pas `Fin.append`/`finSumFinEquiv` — le passage `Fin kA ⊕ Fin kB → Fin (kA+kB)` est
géré automatiquement par la version générique du Sous-lemme 1).

**EN.** Sublemma 5 (add_isOrtho): the only point in this file where an
orthonormal-basis concatenation is actually constructed by hand, using
Sum.elim rather than Fin.append/finSumFinEquiv. The passage
Fin kA ⊕ Fin kB → Fin (kA+kB) is handled automatically by the generic
version of Sublemma 1.
-/
private theorem frameSum_add_isOrtho {g : Proj1 n → ℝ} (hg : IsFrameFunctionOnLines g)
    (A B : Submodule ℂ (H n)) (hAB : A ⟂ B) :
    frameSum g (A ⊔ B) = frameSum g A + frameSum g B := by
  set vA : Fin (Module.finrank ℂ A) → H n := fun i => ((stdOrthonormalBasis ℂ A) i : H n) with hvA
  set vB : Fin (Module.finrank ℂ B) → H n := fun i => ((stdOrthonormalBasis ℂ B) i : H n) with hvB
  have hvAmem : ∀ i, vA i ∈ A := fun i => (stdOrthonormalBasis ℂ A i).2
  have hvBmem : ∀ i, vB i ∈ B := fun i => (stdOrthonormalBasis ℂ B i).2
  have hcross : ∀ i j, ⟪vA i, vB j⟫_ℂ = 0 :=
    fun i j => Submodule.isOrtho_iff_inner_eq.mp hAB _ (hvAmem i) _ (hvBmem j)
  have hcross' : ∀ i j, ⟪vB j, vA i⟫_ℂ = 0 := by
    intro i j
    have h := congrArg (starRingEnd ℂ) (hcross i j)
    rwa [inner_conj_symm, map_zero] at h
  have hw : Orthonormal ℂ (Sum.elim vA vB) := by
    constructor
    · rintro (i | i)
      · exact (orthonormal_stdBasis_coe A).1 i
      · exact (orthonormal_stdBasis_coe B).1 i
    · rintro (i | i) (j | j) hij
      · exact (orthonormal_stdBasis_coe A).2 (fun h => hij (by rw [h]))
      · exact hcross i j
      · exact hcross' j i
      · exact (orthonormal_stdBasis_coe B).2 (fun h => hij (by rw [h]))
  have hspan : Submodule.span ℂ (Set.range (Sum.elim vA vB)) = A ⊔ B := by
    rw [Set.Sum.elim_range, Submodule.span_union, span_stdBasis_coe A, span_stdBasis_coe B]
  have hAB_inf : A ⊓ B = ⊥ := hAB.disjoint.eq_bot
  have hcardAB : Module.finrank ℂ ↥(A ⊔ B) = Module.finrank ℂ A + Module.finrank ℂ B := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq A B
    rw [hAB_inf] at h
    simpa using h
  have hcard : Fintype.card (Fin (Module.finrank ℂ A) ⊕ Fin (Module.finrank ℂ B))
      = Module.finrank ℂ ↥(A ⊔ B) := by
    rw [hcardAB]; simp
  rw [frameSum_eq_sum_of_orthonormal_spanning hg hcard (Sum.elim vA vB) hw hspan,
    Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rfl

/--
**FR.** La restriction de `μ := frameSum g` à `Proj1 n` redonne exactement `g`.

**EN.** The restriction of μ := frameSum g to Proj1 n is exactly g.
-/
private theorem frameSum_proj1 {g : Proj1 n → ℝ} (hg : IsFrameFunctionOnLines g)
    (P : Proj1 n) : frameSum g (P : Submodule ℂ (H n)) = g P := by
  obtain ⟨x, hx, hxP⟩ := exists_unit_vector_of_proj1 P
  have hcard : Fintype.card Unit = Module.finrank ℂ (P : Submodule ℂ (H n)) := by
    rw [P.2]; simp
  have hv : Orthonormal ℂ (fun _ : Unit => x) := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i; fin_cases j
    simp [hx]
  have hspan : Submodule.span ℂ (Set.range (fun _ : Unit => x)) = (P : Submodule ℂ (H n)) := by
    rw [hxP]
    congr 1
    simp [Set.range_const]
  rw [frameSum_eq_sum_of_orthonormal_spanning hg hcard (fun _ : Unit => x) hv hspan]
  simp [gv_of_norm_one hx]
  have : Proj1.mk_unit x hx = P := Subtype.ext hxP.symm
  rw [this]

/--
**FR.** **U3a** : une fonction-cadre définie seulement sur les droites, additive sur
toute base orthonormée, s'étend en un `ProjMeasure n` complet qui coïncide avec
elle sur chaque droite.

**EN.** U3a: a frame function defined only on lines and additive over every
orthonormal basis extends to a full ProjMeasure n that agrees with it on
every line.
-/
theorem exists_projMeasure_of_frameFunctionOnLines (n : ℕ) (g : Proj1 n → ℝ)
    (hg : IsFrameFunctionOnLines g) :
    ∃ m : ProjMeasure n, ∀ P : Proj1 n, m.μ (P : Submodule ℂ (H n)) = g P :=
  ⟨⟨frameSum g, frameSum_nonneg hg, frameSum_top hg, frameSum_add_isOrtho hg⟩,
    frameSum_proj1 hg⟩

end
end QuantumFoundations.Uhlhorn
