import QuantumFoundations.Wigner.Main
import Gleason.Main

/-!
**FR.** # Définitions U0 — Uhlhorn / Corollaire 1.2 de Šemrl

Toutes les définitions réutilisent au maximum ce qui existe déjà : `H n`, `wigner`,
`IsWignerMap` (`QuantumFoundations.Wigner`) ; `Submodule ℂ (H n)`, `projL`,
`bornValue`, `ProjMeasure`, `Gleason.gleason` (`Gleason`, dépendance épinglée).
Aucun wrapper `rankOne`/structure bundlée n'existe côté `gleason` pour « projection
de rang 1 » — les projections y sont représentées par des `Submodule ℂ (H n)`
(cf. `ProjMeasure`/`bornValue`/`projL`), jamais par un type dédié. `Proj1` ci-dessous
suit cette convention plutôt que d'en introduire une nouvelle.

Convention retenue pour « symétrie de Wigner en langage de projections »
(`IsWignerSymmetryProj`, Option 1 validée) : égalité de DROITES
`φ(ℂ∙x) = ℂ∙(Ux)`, PAS l'égalité opératorielle littérale `φ(P) = U P U*`. Les deux
formulations sont mathématiquement équivalentes pour des projections de rang 1
(la droite détermine la projection) ; l'Option 1 évite d'avoir à définir
`LinearMap.adjoint` d'une équivalence semilinéaire (`≃ₛₗᵢ[starRingEnd ℂ]`), un point
d'API jamais rencontré dans ce projet. L'Option 2 (opératorielle) est laissée en
remarque pour une passe ultérieure si le papier final en a besoin explicitement.

**EN.** # Definitions U0 — Uhlhorn / Šemrl's Corollary 1.2

All definitions reuse existing infrastructure as extensively as possible:
H n, wigner, and IsWignerMap (QuantumFoundations.Wigner);
Submodule ℂ (H n), projL, bornValue, ProjMeasure, and
Gleason.gleason (Gleason, pinned dependency). The gleason library has
no rankOne wrapper or bundled structure for “rank-one projection”:
projections are represented there by Submodule ℂ (H n) values
(see ProjMeasure/bornValue/projL), never by a dedicated type. Proj1
below follows this convention rather than introducing a new one.

The adopted convention for “Wigner symmetry in projection language”
(IsWignerSymmetryProj, validated Option 1) is equality of LINES,
φ(ℂ∙x) = ℂ∙(Ux), NOT the literal operator equality φ(P) = U P U*. The two
formulations are mathematically equivalent for rank-one projections, since
the line determines the projection. Option 1 avoids defining the
LinearMap.adjoint of a semilinear equivalence
(≃ₛₗᵢ[starRingEnd ℂ]), an API point never encountered in this project.
Option 2, the operator formulation, is left as a remark for a later pass if
the final paper explicitly requires it.
-/

namespace QuantumFoundations.Uhlhorn

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ}

private theorem ne_zero_of_norm_eq_one {x : H n} (hx : ‖x‖ = 1) : x ≠ 0 := by
  intro h; rw [h, norm_zero] at hx; exact one_ne_zero hx.symm

/--
**FR.** Un vecteur unitaire force `n ≥ 1` (`H 0` est `Subsingleton`). Public : partagé
entre U2 (`Spectral.lean`) et U3b (`GleasonTwice.lean`), toutes deux basées sur
une complétion de base orthonormée via `exists_orthonormalBasis_extension_complex`.

**EN.** A unit vector forces n ≥ 1 (H 0 is Subsingleton). Public: shared
between U2 (Spectral.lean) and U3b (GleasonTwice.lean), both of which use
completion to an orthonormal basis through
exists_orthonormalBasis_extension_complex.
-/
theorem one_le_of_norm_eq_one {x : H n} (hx : ‖x‖ = 1) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · exfalso
    subst h0
    have hx0 : x = 0 := Subsingleton.elim _ _
    rw [hx0] at hx
    simp at hx
  · exact h0

/--
**FR.** Une projection de rang 1, représentée comme sous-espace de dimension 1 — pas de
wrapper `rankOne` dédié, convention identique à `Gleason.ProjMeasure`/`bornValue`.

**EN.** A rank-one projection, represented as a one-dimensional subspace—there
is no dedicated rankOne wrapper, in accordance with
Gleason.ProjMeasure/bornValue.
-/
abbrev Proj1 (n : ℕ) := {A : Submodule ℂ (H n) // Module.finrank ℂ A = 1}

/--
**FR.** La projection de rang 1 portée par un vecteur unitaire `x`.

**EN.** The rank-one projection supported on a unit vector x.
-/
def Proj1.mk_unit (x : H n) (hx : ‖x‖ = 1) : Proj1 n :=
  ⟨ℂ ∙ x, finrank_span_singleton (ne_zero_of_norm_eq_one hx)⟩

/--
**FR.** Tout `P : Proj1 n` est porté par un vecteur unitaire canonique
(`eq_span_singleton_of_mem_of_finrank_eq_one`, pas de recours à
`stdOrthonormalBasis` — évite toute gymnastique d'index pour ce cas `finrank = 1`).
Public : partagé entre U1 (`WignerProjectionForm.lean`) et U3a
(`GleasonExtend.lean`) — évite la duplication et une dépendance de fichier
gênante de U1 (indépendant du reste) vers U3a.

**EN.** Every P : Proj1 n is supported on a canonical unit vector
(eq_span_singleton_of_mem_of_finrank_eq_one, without using
stdOrthonormalBasis, thus avoiding index manipulation in this
finrank = 1 case). Public: shared between U1
(WignerProjectionForm.lean) and U3a (GleasonExtend.lean), avoiding both
duplication and an undesirable dependency from U1, which is independent of
the remainder, to U3a.
-/
theorem exists_unit_vector_of_proj1 (P : Proj1 n) :
    ∃ x : H n, ‖x‖ = 1 ∧ (P : Submodule ℂ (H n)) = ℂ ∙ x := by
  have hne : (P : Submodule ℂ (H n)) ≠ ⊥ := by
    intro hbot
    have h1 := P.2
    rw [hbot] at h1
    simp at h1
  obtain ⟨w, hwP, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨(‖w‖⁻¹ : ℂ) • w, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg w),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)]
  · rw [Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr
      (by exact_mod_cast norm_ne_zero_iff.mpr hw0 : (‖w‖ : ℂ) ≠ 0)).inv]
    exact eq_span_singleton_of_mem_of_finrank_eq_one P.2 hwP hw0

/--
**FR.** `tr(PQ)`, exprimé via l'infrastructure Gleason existante (`projL`/`bornValue`) :
`bornValue (projL P) Q = Re tr(projL P ∘ₗ projL Q)`.

**EN.** tr(PQ), expressed through the existing Gleason infrastructure
(projL/bornValue):
bornValue (projL P) Q = Re tr(projL P ∘ₗ projL Q).
-/
def TraceProd (P Q : Proj1 n) : ℝ :=
  bornValue (projL (P : Submodule ℂ (H n))) (Q : Submodule ℂ (H n))

/--
**FR.** La projection orthogonale sur la droite de `x` unitaire, en formule fermée.
Public : partagé entre U1 (`WignerProjectionForm.lean`) et U2 (`Spectral.lean`).

**EN.** The orthogonal projection onto the line spanned by the unit vector x,
in closed form. Public: shared between U1 (WignerProjectionForm.lean) and
U2 (Spectral.lean).
-/
theorem projL_singleton_unit (x y : H n) (hx : ‖x‖ = 1) :
    projL (ℂ ∙ x) y = ⟪x, y⟫_ℂ • x := by
  unfold projL
  rw [ContinuousLinearMap.coe_coe, Submodule.starProjection_singleton ℂ]
  simp [hx]

/--
**FR.** Un opérateur densité a une forme quadratique bornée par `1` en tout vecteur
unitaire — décomposition de trace autour de `x`. Public : partagé entre U3b
(`GleasonTwice.lean`) et B3 (`BornRule/Pinning.lean`), relocalisé ici lors de
B3 (même pattern que `exists_unit_vector_of_proj1`/`projL_singleton_unit`).

**EN.** A density operator has quadratic form bounded above by 1 on every
unit vector, by decomposing the trace around x. Public: shared between U3b
(GleasonTwice.lean) and B3 (BornRule/Pinning.lean), and moved here during
B3 following the same pattern as
exists_unit_vector_of_proj1/projL_singleton_unit.
-/
theorem density_inner_le_one {ρ : H n →ₗ[ℂ] H n} (hρ : IsDensityOperator ρ)
    {x : H n} (hx : ‖x‖ = 1) : (⟪ρ x, x⟫_ℂ).re ≤ 1 := by
  have hn1 : 1 ≤ n := one_le_of_norm_eq_one hx
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_extension_complex hn1 (fun _ : Fin 1 => x)
    (by rw [orthonormal_iff_ite]; intro i j; fin_cases i; fin_cases j; simp [hx])
  set i0 : Fin n := Fin.castLE hn1 (0 : Fin 1) with hi0
  have hbi0 : b i0 = x := hb 0
  have htrace_sum : LinearMap.trace ℂ (H n) ρ = ∑ i, ⟪b i, ρ (b i)⟫_ℂ :=
    LinearMap.trace_eq_sum_inner ρ b
  have hnn : ∀ i, 0 ≤ (⟪b i, ρ (b i)⟫_ℂ).re := by
    intro i
    rw [← hρ.symmetric (b i) (b i)]
    exact hρ.nonneg (b i)
  have hle : (⟪b i0, ρ (b i0)⟫_ℂ).re ≤ ∑ i, (⟪b i, ρ (b i)⟫_ℂ).re :=
    Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ i0)
  rw [← Complex.re_sum, ← htrace_sum, hρ.trace_one] at hle
  rw [hbi0] at hle
  rw [hρ.symmetric x x]
  simpa using hle

private theorem sub_nonneg_of_density {ρ : H n →ₗ[ℂ] H n} (hρ : IsDensityOperator ρ) (z : H n) :
    0 ≤ (⟪(1 - ρ) z, z⟫_ℂ).re := by
  rcases eq_or_ne z 0 with hz0 | hz0
  · simp [hz0]
  · set x : H n := (‖z‖⁻¹ : ℂ) • z with hx_def
    have hxnorm : ‖x‖ = 1 := by
      rw [hx_def, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg z), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz0)]
    have hz_eq : z = (‖z‖ : ℂ) • x := by
      rw [hx_def, smul_smul, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
        mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz0), Complex.ofReal_one, one_smul]
    have hinner : ⟪ρ z, z⟫_ℂ = (((‖z‖ : ℝ) ^ 2 : ℝ) : ℂ) * ⟪ρ x, x⟫_ℂ := by
      conv_lhs => rw [hz_eq]
      rw [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
      push_cast; ring
    have hle := density_inner_le_one hρ hxnorm
    have hzz : ⟪z, z⟫_ℂ = (((‖z‖ : ℝ) ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    rw [LinearMap.sub_apply, Module.End.one_apply, inner_sub_left, hzz, hinner,
      Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re]
    nlinarith [sq_nonneg (‖z‖ : ℝ), hle]

/--
**FR.** **Densité ⟹ effet** (absent de `gleason-theorem-lean`, confirmé en
reconnaissance U3b) : positivité + trace `1` en dimension finie force `≤ 1`
(les valeurs propres d'une densité sont positives et somment à `1`, donc
chacune est `≤ 1`). Public depuis B3 (même relocalisation que ci-dessus).

**EN.** Density ⟹ effect (absent from gleason-theorem-lean, as confirmed
during U3b reconnaissance): positivity + trace 1 in finite
dimension forces ≤ 1 (the eigenvalues of a density operator are
nonnegative and sum to 1, hence each is ≤ 1). Public since B3, with the
same relocation as above.
-/
theorem isEffect_of_isDensityOperator {ρ : H n →ₗ[ℂ] H n} (hρ : IsDensityOperator ρ) :
    IsEffect ρ := by
  have h1 : IsPositiveOp ρ := ⟨hρ.symmetric, hρ.nonneg⟩
  have h2symm : LinearMap.IsSymmetric (1 - ρ) := LinearMap.IsSymmetric.one.sub hρ.symmetric
  have h2nn : ∀ z, 0 ≤ (⟪(1 - ρ) z, z⟫_ℂ).re := sub_nonneg_of_density hρ
  have h2 : IsPositiveOp (1 - ρ) := ⟨h2symm, h2nn⟩
  exact ⟨h1, h2⟩

/--
**FR.** `φ` préserve l'orthogonalité DANS UN SEUL SENS : `PQ = 0 ⟹ φ(P)φ(Q) = 0`. Ni
injectivité ni surjectivité supposées sur `φ`.

**EN.** φ preserves orthogonality IN ONE DIRECTION:
PQ = 0 ⟹ φ(P)φ(Q) = 0. Neither injectivity nor surjectivity of φ is
assumed.
-/
def PreservesOrthogonality (φ : Proj1 n → Proj1 n) : Prop :=
  ∀ P Q : Proj1 n, (P : Submodule ℂ (H n)) ⟂ (Q : Submodule ℂ (H n)) →
    (φ P : Submodule ℂ (H n)) ⟂ (φ Q : Submodule ℂ (H n))

/--
**FR.** **Symétrie de Wigner, en langage de projections** (Option 1 : égalité de
droites — voir note d'en-tête).

**EN.** Wigner symmetry in projection language (Option 1: equality of
lines; see the header note).
-/
def IsWignerSymmetryProj (φ : Proj1 n → Proj1 n) : Prop :=
  (∃ U : H n ≃ₗᵢ[ℂ] H n, ∀ x : H n, ∀ hx : ‖x‖ = 1,
      (φ (Proj1.mk_unit x hx) : Submodule ℂ (H n)) = ℂ ∙ (U x))
∨ (∃ U : H n ≃ₛₗᵢ[starRingEnd ℂ] H n, ∀ x : H n, ∀ hx : ‖x‖ = 1,
      (φ (Proj1.mk_unit x hx) : Submodule ℂ (H n)) = ℂ ∙ (U x))

/--
**FR.** Une fonction-cadre sur les droites : positive, et sommant à `1` sur TOUTE base
orthonormée de l'espace ambiant (analogue de `IsCFrameFunction`/`ProjMeasure`, mais
définie seulement sur `Proj1 n`, pas sur tous les sous-espaces — cf. U3a).

**EN.** A frame function on lines: nonnegative and summing to 1 over EVERY
orthonormal basis of the ambient space (analogous to
IsCFrameFunction/ProjMeasure, but defined only on Proj1 n, not on all
subspaces; see U3a).
-/
def IsFrameFunctionOnLines (g : Proj1 n → ℝ) : Prop :=
  (∀ P, 0 ≤ g P) ∧
  (∀ b : OrthonormalBasis (Fin n) ℂ (H n),
    ∑ i, g (Proj1.mk_unit (b i) (b.norm_eq_one i)) = 1)

/--
**FR.** `φ` envoie tout système orthonormé complet (COSP — en dimension finie, toute
base orthonormée) sur un COSP.

**EN.** φ sends every complete orthonormal system (COSP—in finite dimension,
every orthonormal basis) to a COSP.
-/
def SendsONBToONB (φ : Proj1 n → Proj1 n) : Prop :=
  ∀ b : OrthonormalBasis (Fin n) ℂ (H n),
    ∃ b' : OrthonormalBasis (Fin n) ℂ (H n),
      ∀ i, (φ (Proj1.mk_unit (b i) (b.norm_eq_one i)) : Submodule ℂ (H n)) = ℂ ∙ (b' i)

end
end QuantumFoundations.Uhlhorn
