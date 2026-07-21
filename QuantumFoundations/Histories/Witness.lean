import QuantumFoundations.Histories.Basic

/-!
**FR.** # K2 — Witness : les deux ensembles cohérents de Kent

Données explicites en dimension 3 (`H 3`), vecteurs NON normalisés (décision de
conception de la reconnaissance : toute la contrariété se lit sur des rapports
où les normalisations `1/√3` s'annulent — éviter `Real.sqrt` partout où c'est
possible) :
* `ψ₀ := e₀+e₁+e₂` (préparation), `φ₀ := e₀+e₁−e₂` (post-sélection).
* `P i := ℂ∙(e i)` pour `i ∈ {0,1}` (les deux propositions mutuellement
  orthogonales, `P 0 ⟂ P 1` immédiat), `F := ℂ∙φ₀`.
* `S i := [Perspective.binary (P i), Perspective.binary F]`, famille cohérente
  à 2 étages pour chaque `i`.

## Écart vs la feuille de route : un seul but ouvert paramétré plutôt que deux

La route prévoyait deux buts ouverts distincts `S₁_consistent`/`S₂_consistent`,
tout en autorisant explicitement leur factorisation en un lemme paramétré par
`i` « si la duplication est lourde » (les deux preuves ne diffèrent que par
l'indice `i ∈ {0,1}` et l'annulation clé `⟪φ₀, e 1 + e 2⟫ = 0` /
`⟪φ₀, e 0 + e 2⟫ = 0`, structurellement identiques). Option retenue : un seul
`S_consistent (i : Fin 3)`, spécialisé en `S1_consistent`/`S2_consistent`
ci-dessous sans laisser de but supplémentaire ouvert. K2 ne compte donc qu'un
seul but ouvert physique (au lieu de deux), qui décharge néanmoins les deux
faits demandés par le plan.

## Correction de l'énoncé (règle 2 du projet) : hypothèse `i = 0 ∨ i = 1` ajoutée

Le squelette K0 énonçait `S_consistent (i : Fin 3) : IsConsistent ψ₀ (S i)`
SANS restriction sur `i`. Ceci est FAUX pour `i = 2` : l'annulation clé
`⟪φ₀, ψ₀ - e i⟫ = 1 - ⟪φ₀, e i⟫` s'annule seulement pour `i ∈ {0,1}`
(`⟪φ₀,e 0⟫ = ⟪φ₀,e 1⟫ = 1` mais `⟪φ₀,e 2⟫ = -1`, vérifié explicitement par
calcul — `φ₀ = e0+e1-e2` porte un signe négatif sur `e2`). La famille `S 2`
n'est donc probablement PAS cohérente pour `ψ₀`. Correction (pas un
affaiblissement dissimulé) : ajout de l'hypothèse `i = 0 ∨ i = 1`, seul
domaine où le témoin est utilisé (`S1_consistent`/`S2_consistent`
l'instancient trivialement).

**EN.** # K2 — Witness: Kent's two consistent sets

Explicit data in dimension 3 (H 3), using NONNORMALIZED vectors (a design
decision from reconnaissance: the entire contrary-inference construction is
expressed through ratios in which the normalization factors 1/√3 cancel,
so Real.sqrt is avoided wherever possible):
* ψ₀ := e₀+e₁+e₂ (preparation), φ₀ := e₀+e₁−e₂ (postselection).
* P i := ℂ∙(e i) for i ∈ {0,1} (the two mutually orthogonal propositions,
 with P 0 ⟂ P 1 immediate), and F := ℂ∙φ₀.
* S i := [Perspective.binary (P i), Perspective.binary F], a consistent
 two-stage family for each i.

## Deviation from the roadmap: one parameterized open goal rather than two

The roadmap specified two distinct open goals,
S₁_consistent/S₂_consistent, while explicitly allowing them to be factored
into a lemma parameterized by i “if duplication is substantial.” The two
proofs differ only in the index i ∈ {0,1} and in the key cancellations
⟪φ₀, e 1 + e 2⟫ = 0 / ⟪φ₀, e 0 + e 2⟫ = 0, which are structurally
identical. The selected option is therefore a single
S_consistent (i : Fin 3), specialized below to
S1_consistent/S2_consistent without leaving an additional open goal.
Thus K2 has only one physical open goal rather than two, while still
discharging both facts required by the plan.

## Correction to the statement (project rule 2): hypothesis
i = 0 ∨ i = 1 added

The K0 skeleton stated S_consistent (i : Fin 3) : IsConsistent ψ₀ (S i)
WITHOUT restricting i. This is FALSE for i = 2: the key cancellation
⟪φ₀, ψ₀ - e i⟫ = 1 - ⟪φ₀, e i⟫ holds only for i ∈ {0,1}
(⟪φ₀,e 0⟫ = ⟪φ₀,e 1⟫ = 1, whereas ⟪φ₀,e 2⟫ = -1, as verified by an
explicit calculation—φ₀ = e0+e1-e2 has a negative sign on e2). The
family S 2 is therefore probably NOT consistent for ψ₀. The correction,
which is not a concealed weakening, is to add the hypothesis
i = 0 ∨ i = 1, precisely the only domain in which the witness is used
(S1_consistent/S2_consistent instantiate it trivially).
-/

namespace QuantumFoundations.Histories

open scoped InnerProductSpace
open Gleason QuantumFoundations.BornRule

noncomputable section

/--
**FR.** Base canonique (non normalisée en soi, mais chaque `e i` est unitaire) de
`H 3`.

**EN.** Canonical basis of H 3 (the basis as a whole is not a normalized
state, but every e i is a unit vector).
-/
def e (i : Fin 3) : H 3 := EuclideanSpace.single i (1 : ℂ)

theorem e_ne_zero (i : Fin 3) : e i ≠ 0 := by
  unfold e
  rw [Ne, PiLp.single_eq_zero_iff]
  norm_num

theorem e_ortho {i j : Fin 3} (hij : i ≠ j) : ⟪e i, e j⟫_ℂ = 0 := by
  unfold e
  rw [EuclideanSpace.inner_single_left]
  simp [hij]

/--
**FR.** Préparation (non normalisée) : `ψ₀ := e₀+e₁+e₂`.

**EN.** Preparation (not normalized): ψ₀ := e₀+e₁+e₂.
-/
def ψ₀ : H 3 := e 0 + e 1 + e 2

/--
**FR.** Post-sélection (non normalisée) : `φ₀ := e₀+e₁−e₂`.

**EN.** Postselection (not normalized): φ₀ := e₀+e₁−e₂.
-/
def φ₀ : H 3 := e 0 + e 1 - e 2

theorem φ₀_inner_self : ⟪φ₀, φ₀⟫_ℂ = 3 := by
  unfold φ₀ e
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    EuclideanSpace.inner_single_left, map_one, PiLp.single_apply]
  norm_num [Fin.ext_iff]

/--
**FR.** `‖φ₀‖² = 3`, en langage réel (passage depuis `φ₀_inner_self` via
`inner_self_eq_norm_sq_to_K`). Public : réutilisé par K3
(`ContraryInferences.lean`).

**EN.** ‖φ₀‖² = 3, expressed over the reals (transported from
φ₀_inner_self via inner_self_eq_norm_sq_to_K). Public: reused by K3
(ContraryInferences.lean).
-/
theorem φ₀_norm_sq : ‖φ₀‖ ^ 2 = 3 := by
  have h4 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) φ₀
  rw [φ₀_inner_self] at h4
  have h5 : ((‖φ₀‖ ^ 2 : ℝ) : ℂ) = ((3 : ℝ) : ℂ) := by
    push_cast
    linear_combination -h4
  exact Complex.ofReal_injective h5

theorem φ₀_ne_zero : φ₀ ≠ 0 := by
  intro h
  have := φ₀_inner_self
  rw [h] at this
  simp at this

/--
**FR.** `P i := ℂ∙(e i)`, `i ∈ Fin 3` (seuls `i = 0, 1` servent au témoin).

**EN.** P i := ℂ∙(e i), for i ∈ Fin 3 (only i = 0, 1 are used in the witness).
-/
def P (i : Fin 3) : Submodule ℂ (H 3) := ℂ ∙ (e i)

/--
**FR.** Post-sélection : `F := ℂ∙φ₀`.

**EN.** Postselection: F := ℂ∙φ₀.
-/
def F : Submodule ℂ (H 3) := ℂ ∙ φ₀

theorem P_ne_bot (i : Fin 3) : P i ≠ ⊥ := by
  unfold P; rw [Submodule.ne_bot_iff]
  exact ⟨e i, Submodule.mem_span_singleton_self _, e_ne_zero i⟩

theorem P_ne_top (i : Fin 3) : P i ≠ ⊤ := by
  unfold P
  intro htop
  have h1 : Module.finrank ℂ (ℂ ∙ (e i)) = 1 := finrank_span_singleton (e_ne_zero i)
  rw [htop, finrank_top] at h1
  simp at h1

theorem F_ne_bot : F ≠ ⊥ := by
  unfold F; rw [Submodule.ne_bot_iff]
  exact ⟨φ₀, Submodule.mem_span_singleton_self _, φ₀_ne_zero⟩

theorem F_ne_top : F ≠ ⊤ := by
  unfold F
  intro htop
  have h1 : Module.finrank ℂ (ℂ ∙ φ₀) = 1 := finrank_span_singleton φ₀_ne_zero
  rw [htop, finrank_top] at h1
  simp at h1

/--
**FR.** Les deux propositions du témoin de Kent sont mutuellement orthogonales
(immédiat : `e 0 ⊥ e 1`).

**EN.** The two propositions in Kent's witness are mutually orthogonal
(immediate from e 0 ⊥ e 1).
-/
theorem P_ortho {i j : Fin 3} (hij : i ≠ j) : P i ⟂ P j := by
  unfold P
  rw [Submodule.isOrtho_iff_le]
  intro x hx
  rw [Submodule.mem_orthogonal]
  intro y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [inner_smul_left, inner_smul_right, e_ortho hij.symm]
  ring

/--
**FR.** Étage initial `i` : perspective binaire `{P i, (P i)ᗮ}`.

**EN.** Initial stage i: the binary perspective {P i, (P i)ᗮ}.
-/
def Dstage (i : Fin 3) : Perspective 3 := Perspective.binary (P i) (P_ne_bot i) (P_ne_top i)

/--
**FR.** Étage final (post-sélection) : perspective binaire `{F, Fᗮ}`.

**EN.** Final stage (postselection): the binary perspective {F, Fᗮ}.
-/
def DF : Perspective 3 := Perspective.binary F F_ne_bot F_ne_top

/--
**FR.** Famille à 2 étages `Sᵢ := [{P i, (P i)ᗮ}, {F, Fᗮ}]`.

**EN.** Two-stage family Sᵢ := [{P i, (P i)ᗮ}, {F, Fᗮ}].
-/
def S (i : Fin 3) : Fin 2 → Perspective 3 := ![Dstage i, DF]

/--
**FR.** `projL Aᗮ = 1 - projL A` (Mathlib : `Submodule.starProjection_orthogonal'`),
transporté en langage `LinearMap`. Public : réutilisé par K3
(`ContraryInferences.lean`).

**EN.** projL Aᗮ = 1 - projL A
(Mathlib: Submodule.starProjection_orthogonal'), transported into
LinearMap language. Public: reused by K3 (ContraryInferences.lean).
-/
theorem projL_compl (A : Submodule ℂ (H 3)) (x : H 3) :
    projL Aᗮ x = x - projL A x := by
  show (Aᗮ.starProjection : H 3 →L[ℂ] H 3) x = x - (A.starProjection : H 3 →L[ℂ] H 3) x
  rw [Submodule.starProjection_orthogonal']
  simp

private theorem psi0_inner_e (i : Fin 3) : ⟪ψ₀, e i⟫_ℂ = 1 := by
  unfold ψ₀ e
  simp only [inner_add_left, EuclideanSpace.inner_single_left, map_one, PiLp.single_apply]
  fin_cases i <;> norm_num [Fin.ext_iff]

private theorem e_inner_psi0 (i : Fin 3) : ⟪e i, ψ₀⟫_ℂ = 1 := by
  unfold ψ₀ e
  simp only [inner_add_right, EuclideanSpace.inner_single_left, map_one, PiLp.single_apply]
  fin_cases i <;> norm_num [Fin.ext_iff]

private theorem e_inner_e_self (i : Fin 3) : ⟪e i, e i⟫_ℂ = 1 := by
  unfold e
  rw [EuclideanSpace.inner_single_left]
  simp

private theorem psi0_inner_phi0 : ⟪ψ₀, φ₀⟫_ℂ = 1 := by
  unfold ψ₀ φ₀ e
  simp only [inner_sub_right, inner_add_left, inner_add_right, EuclideanSpace.inner_single_left,
    map_one, PiLp.single_apply]
  norm_num [Fin.ext_iff]

private theorem phi0_inner_psi0 : ⟪φ₀, ψ₀⟫_ℂ = 1 := by
  unfold ψ₀ φ₀ e
  simp only [inner_sub_left, inner_add_left, inner_add_right, EuclideanSpace.inner_single_left,
    map_one, PiLp.single_apply]
  norm_num [Fin.ext_iff]

/--
**FR.** Amplitude clé : `⟪e i, φ₀⟫ = 1` pour `i ∈ {0,1}` (`= -1` pour `i = 2`, hors
scope du témoin — c'est la raison de la restriction `i = 0 ∨ i = 1`).

**EN.** Key amplitude: ⟪e i, φ₀⟫ = 1 for i ∈ {0,1} (= -1 for
i = 2, outside the scope of the witness—this is the reason for the
restriction i = 0 ∨ i = 1).
-/
private theorem e_inner_phi0_01 (i : Fin 3) (hi : i = 0 ∨ i = 1) : ⟪e i, φ₀⟫_ℂ = 1 := by
  rcases hi with rfl | rfl
  · unfold φ₀ e
    simp only [inner_sub_right, inner_add_right, EuclideanSpace.inner_single_left, map_one,
      PiLp.single_apply]
    norm_num [Fin.ext_iff]
  · unfold φ₀ e
    simp only [inner_sub_right, inner_add_right, EuclideanSpace.inner_single_left, map_one,
      PiLp.single_apply]
    norm_num [Fin.ext_iff]

/--
**FR.** Public : réutilisé par K3 (`ContraryInferences.lean`).

**EN.** Public: reused by K3 (ContraryInferences.lean).
-/
theorem phi0_inner_e01 (i : Fin 3) (hi : i = 0 ∨ i = 1) : ⟪φ₀, e i⟫_ℂ = 1 := by
  rcases hi with rfl | rfl
  · unfold φ₀ e
    simp only [inner_sub_left, inner_add_left, EuclideanSpace.inner_single_left, map_one,
      PiLp.single_apply]
    norm_num [Fin.ext_iff]
  · unfold φ₀ e
    simp only [inner_sub_left, inner_add_left, EuclideanSpace.inner_single_left, map_one,
      PiLp.single_apply]
    norm_num [Fin.ext_iff]

private theorem e_norm_one (i : Fin 3) : ‖e i‖ = 1 := by
  unfold e
  rw [PiLp.norm_single]
  simp

/--
**FR.** `projL (P i) ψ₀ = e i` : la branche `P i` de la première étape isole
exactement le `i`-ème vecteur de base (`ψ₀` a un coefficient unité sur
chaque `e j`). Public : réutilisé par K3 (`ContraryInferences.lean`).

**EN.** projL (P i) ψ₀ = e i: the P i branch at the first stage isolates
exactly the ith basis vector (ψ₀ has unit coefficient on every e j).
Public: reused by K3 (ContraryInferences.lean).
-/
theorem P_proj_psi0 (i : Fin 3) : projL (P i) ψ₀ = e i := by
  show (ℂ ∙ e i : Submodule ℂ (H 3)).starProjection ψ₀ = e i
  rw [show ((ℂ ∙ e i : Submodule ℂ (H 3)).starProjection ψ₀)
      = (⟪e i, ψ₀⟫_ℂ / ((‖e i‖ ^ 2 : ℝ) : ℂ)) • e i from Submodule.starProjection_singleton ℂ ψ₀]
  rw [e_inner_psi0, e_norm_one]
  norm_num

/--
**FR.** Formule fermée de `projL F` (vecteur `φ₀` non normalisé, `‖φ₀‖² = 3`, cf.
`φ₀_inner_self`). Public : réutilisé par K3 (`ContraryInferences.lean`).

**EN.** Closed formula for projL F (with the nonnormalized vector φ₀ and
‖φ₀‖² = 3; see φ₀_inner_self). Public: reused by K3
(ContraryInferences.lean).
-/
theorem projL_F_eq (x : H 3) :
    projL F x = (⟪φ₀, x⟫_ℂ / ((‖φ₀‖ ^ 2 : ℝ) : ℂ)) • φ₀ := by
  show (F : Submodule ℂ (H 3)).starProjection x = _
  unfold F
  exact Submodule.starProjection_singleton ℂ x

/--
**FR.** Les deux orthogonalités de `w := ψ₀ - e i` (image de la branche `(P i)ᗮ`
de la première étape) qui pilotent toute la suite : `w ⊥ e i` et `w ⊥ φ₀`
(cette dernière est L'ANNULATION CLÉ du témoin de Kent). Public : réutilisé
par K3 (`ContraryInferences.lean`).

**EN.** The two orthogonality relations for w := ψ₀ - e i, the image of the
first-stage branch (P i)ᗮ, that drive the remainder of the argument:
w ⊥ e i and w ⊥ φ₀ (the latter is THE KEY CANCELLATION in Kent's
witness). Public: reused by K3 (ContraryInferences.lean).
-/
theorem w_ortho (i : Fin 3) (hi : i = 0 ∨ i = 1) :
    ⟪ψ₀ - e i, e i⟫_ℂ = 0 ∧ ⟪ψ₀ - e i, φ₀⟫_ℂ = 0 ∧ ⟪φ₀, ψ₀ - e i⟫_ℂ = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [inner_sub_left, psi0_inner_e, e_inner_e_self]; ring
  · rw [inner_sub_left, psi0_inner_phi0, e_inner_phi0_01 i hi]; ring
  · rw [inner_sub_right, phi0_inner_psi0, phi0_inner_e01 i hi]; ring

private theorem e_ortho_psi0_sub_e (i : Fin 3) : ⟪e i, ψ₀ - e i⟫_ℂ = 0 := by
  rw [inner_sub_right, e_inner_psi0, e_inner_e_self]; ring

/--
**FR.** `projL` est autoadjoint (dérivé en une ligne, reconnaissance A.2).

**EN.** projL is self-adjoint (derived in one line, reconnaissance A.2).
-/
private theorem projL_isSymmetric (c1 : Submodule ℂ (H 3)) : LinearMap.IsSymmetric (projL c1) := by
  intro x y
  show ⟪(c1.starProjection : H 3 →L[ℂ] H 3) x, y⟫_ℂ = ⟪x, (c1.starProjection : H 3 →L[ℂ] H 3) y⟫_ℂ
  exact c1.starProjection_isSymmetric x y

/--
**FR.** Auto-adjonction + idempotence de `projL` : la projection peut s'« absorber »
dans un seul des deux arguments de l'inner product.

**EN.** Self-adjointness + idempotence of projL: the projection can be
“absorbed” into only one of the two arguments of the inner product.
-/
private theorem projL_proj_absorb (c1 : Submodule ℂ (H 3)) (w u : H 3) :
    ⟪projL c1 w, projL c1 u⟫_ℂ = ⟪w, projL c1 u⟫_ℂ := by
  have hidem : projL c1 (projL c1 u) = projL c1 u := by
    show (c1.starProjection : H 3 →L[ℂ] H 3) ((c1.starProjection : H 3 →L[ℂ] H 3) u)
      = (c1.starProjection : H 3 →L[ℂ] H 3) u
    exact congrFun (congrArg DFunLike.coe c1.isIdempotentElem_starProjection.eq) u
  rw [projL_isSymmetric c1 w (projL c1 u), hidem]

/--
**FR.** Pour `c1 ∈ {F, Fᗮ}`, la branche `w := ψ₀ - e i` reste orthogonale à
`projL c1 (e i)` — vrai dans les deux cas grâce à `w_ortho`.

**EN.** For c1 ∈ {F, Fᗮ}, the branch w := ψ₀ - e i remains orthogonal to
projL c1 (e i)—true in both cases by w_ortho.
-/
private theorem w_ortho_projLc1_u (i : Fin 3) (hi : i = 0 ∨ i = 1) (c1 : Submodule ℂ (H 3))
    (hc1 : c1 = F ∨ c1 = Fᗮ) :
    ⟪ψ₀ - e i, projL c1 (e i)⟫_ℂ = 0 := by
  rcases hc1 with rfl | rfl
  · rw [projL_F_eq, inner_smul_right, (w_ortho i hi).2.1]; ring
  · rw [projL_compl, inner_sub_right, projL_F_eq, inner_smul_right, (w_ortho i hi).2.1,
      (w_ortho i hi).1]
    ring

/--
**FR.** Symétrique de `w_ortho_projLc1_u` (ordre des arguments échangé).

**EN.** Symmetric counterpart of w_ortho_projLc1_u, with the arguments exchanged.
-/
private theorem u_ortho_projLc1_w (i : Fin 3) (hi : i = 0 ∨ i = 1) (c1 : Submodule ℂ (H 3))
    (hc1 : c1 = F ∨ c1 = Fᗮ) :
    ⟪e i, projL c1 (ψ₀ - e i)⟫_ℂ = 0 := by
  rcases hc1 with rfl | rfl
  · rw [projL_F_eq, inner_smul_right, (w_ortho i hi).2.2]; ring
  · rw [projL_compl, inner_sub_right, projL_F_eq, inner_smul_right, (w_ortho i hi).2.2,
      e_ortho_psi0_sub_e]
    ring

/--
**FR.** Déroulement de `chainOp` à `L = 2` étages : le dernier étage appliqué en
dernier au premier, conformément à la convention de `Defs.lean`. Public :
réutilisé par K3 (`ContraryInferences.lean`).

**EN.** Unfolding of chainOp for L = 2 stages: the final stage is applied
after the first, in accordance with the convention in Defs.lean. Public:
reused by K3 (ContraryInferences.lean).
-/
theorem chainOp_two_stage (h' : History 3 2) (ψ : H 3) :
    chainOp h' ψ = projL (h' (Fin.last 1)) (projL (h' 0) ψ) := by
  show (Fin.foldl 2 (fun acc t => projL (h' t) ∘ₗ acc) LinearMap.id) ψ
    = projL (h' (Fin.last 1)) (projL (h' 0) ψ)
  rw [Fin.foldl_succ_last]
  simp only [Fin.foldl_succ, Fin.foldl_zero]
  rfl

/--
**FR.** **K2, but ouvert unique.** `Sᵢ` est cohérente pour `ψ₀`, pour `i ∈ {0,1}`
(voir correction de l'énoncé en en-tête de fichier). Par
`decFunctional_last_stage_orthogonal` (K1(a)), seules les paires d'histoires
différant à l'étage `0` restent à examiner ; l'annulation clé est
`⟪φ₀, projL (P i)ᗮ ψ₀⟫ = 0`.

**EN.** K2, unique open goal. Sᵢ is consistent for ψ₀ when
i ∈ {0,1} (see the correction to the statement in the file header). By
decFunctional_last_stage_orthogonal (K1(a)), only pairs of histories that
differ at stage 0 remain to be considered; the key cancellation is
⟪φ₀, projL (P i)ᗮ ψ₀⟫ = 0.
-/
theorem S_consistent (i : Fin 3) (hi : i = 0 ∨ i = 1) : IsConsistent ψ₀ (S i) := by
  intro h k hh hk hne
  by_cases hlast : h (Fin.last 1) ≠ k (Fin.last 1)
  · exact decFunctional_last_stage_orthogonal (S i) ψ₀ h k hh hk hlast
  push Not at hlast
  have hne0 : h 0 ≠ k 0 := fun heq => hne (funext fun t => by fin_cases t; exacts [heq, hlast])
  have hh0 : h 0 = P i ∨ h 0 = (P i)ᗮ := by
    have := hh 0
    simp only [S, Dstage, Matrix.cons_val_zero] at this
    simpa [Perspective.binary] using this
  have hk0 : k 0 = P i ∨ k 0 = (P i)ᗮ := by
    have := hk 0
    simp only [S, Dstage, Matrix.cons_val_zero] at this
    simpa [Perspective.binary] using this
  have hh1 : h (Fin.last 1) = F ∨ h (Fin.last 1) = Fᗮ := by
    have := hh (Fin.last 1)
    simp only [S, DF] at this
    simpa [Perspective.binary] using this
  show ⟪chainOp k ψ₀, chainOp h ψ₀⟫_ℂ = 0
  rw [chainOp_two_stage k ψ₀, chainOp_two_stage h ψ₀, ← hlast]
  rcases hh0 with hh0 | hh0
  · rcases hk0 with hk0 | hk0
    · exact absurd (hh0.trans hk0.symm) hne0
    · rw [hh0, hk0, projL_compl (P i) ψ₀, P_proj_psi0]
      rcases hh1 with hc1 | hc1
      · rw [hc1, projL_proj_absorb]; exact w_ortho_projLc1_u i hi F (Or.inl rfl)
      · rw [hc1, projL_proj_absorb]; exact w_ortho_projLc1_u i hi Fᗮ (Or.inr rfl)
  · rcases hk0 with hk0 | hk0
    · rw [hh0, hk0, projL_compl (P i) ψ₀, P_proj_psi0]
      rcases hh1 with hc1 | hc1
      · rw [hc1, projL_proj_absorb]; exact u_ortho_projLc1_w i hi F (Or.inl rfl)
      · rw [hc1, projL_proj_absorb]; exact u_ortho_projLc1_w i hi Fᗮ (Or.inr rfl)
    · exact absurd (hh0.trans hk0.symm) hne0

/--
**FR.** `S1 := S 0` : famille cohérente construite sur `P 0`.

**EN.** S1 := S 0: the consistent family constructed from P 0.
-/
theorem S1_consistent : IsConsistent ψ₀ (S 0) := S_consistent 0 (Or.inl rfl)

/--
**FR.** `S2 := S 1` : famille cohérente construite sur `P 1`.

**EN.** S2 := S 1: the consistent family constructed from P 1.
-/
theorem S2_consistent : IsConsistent ψ₀ (S 1) := S_consistent 1 (Or.inr rfl)

end
end QuantumFoundations.Histories
