import QuantumFoundations.Naimark.Defs
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
**FR.** # Espace de dilatation `K := ⊕_{i<m} H n`

Choix d'étape 0 : `K₂ := EuclideanSpace ℂ (Fin m × Fin n)` (version plate), retenu sur
`K₁ := PiLp 2 (fun _ : Fin m => H n)` (nested) à friction de preuve égale, pour son
index unique `Fin m × Fin n` (moins de couches `WithLp`/`.ofLp` à traverser dans N3).
Écart documenté vis-à-vis de Watrous : somme directe hilbertienne, pas
produit tensoriel.

**EN.** # Dilation space K := ⊕_{i<m} H n

Step-0 choice: K₂ := EuclideanSpace ℂ (Fin m × Fin n) (flat version) was
selected over K₁ := PiLp 2 (fun _ : Fin m => H n) (nested version) at equal
proof-engineering cost, because its single index Fin m × Fin n avoids
additional WithLp/.ofLp layers in N3. Documented deviation from Watrous:
a Hilbert direct sum, not a tensor product.
-/

namespace QuantumFoundations

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n m : ℕ}

/--
**FR.** Espace de dilatation : somme directe hilbertienne de `m` copies de `H n`,
réalisée à plat comme `EuclideanSpace ℂ (Fin m × Fin n)`.

**EN.** Dilation space: the Hilbert direct sum of m copies of H n,
implemented in flat form as EuclideanSpace ℂ (Fin m × Fin n).
-/
abbrev DilSpace (n m : ℕ) := EuclideanSpace ℂ (Fin m × Fin n)

/--
**FR.** Injection de `H n` dans le `i`-ème bloc de `DilSpace n m`.

**EN.** Injection of H n into the ith block of DilSpace n m.
-/
def singleL (n m : ℕ) (i : Fin m) : H n →ₗ[ℂ] DilSpace n m where
  toFun x := WithLp.toLp 2 (fun p : Fin m × Fin n => if p.1 = i then x p.2 else 0)
  map_add' x y := by
    rw [← WithLp.toLp_add]; congr 1; funext p; by_cases h : p.1 = i <;> simp [h]
  map_smul' c x := by
    rw [← WithLp.toLp_smul]; congr 1; funext p; by_cases h : p.1 = i <;> simp [h]

/--
**FR.** Projection de `DilSpace n m` sur son `i`-ème bloc, à valeurs dans `H n`.

**EN.** Projection from DilSpace n m onto its ith block, with values in H n.
-/
def coordL (n m : ℕ) (i : Fin m) : DilSpace n m →ₗ[ℂ] H n where
  toFun w := WithLp.toLp 2 (fun k : Fin n => w (i, k))
  map_add' w w' := by rw [← WithLp.toLp_add]; congr 1
  map_smul' c w := by rw [← WithLp.toLp_smul]; congr 1

/--
**FR.** `coordL i` est l'adjoint formel de `singleL i` (produit scalaire) : calcul-pivot,
la somme sur `Fin m × Fin n` se réduit au bloc `i` par construction de `singleL`.

**EN.** coordL i is the formal adjoint of singleL i with respect to the
inner product. This is the pivotal computation: by construction of singleL,
the sum over Fin m × Fin n reduces to block i.
-/
theorem inner_singleL (i : Fin m) (x : H n) (w : DilSpace n m) :
    ⟪singleL n m i x, w⟫_ℂ = ⟪x, coordL n m i w⟫_ℂ := by
  show ⟪(WithLp.toLp 2 (fun p : Fin m × Fin n => if p.1 = i then x p.2 else 0) : DilSpace n m),
    w⟫_ℂ = _
  rw [PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_eq_single i]
  · simp [coordL]
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _
    simp [ha]
  · intro h; exact absurd (Finset.mem_univ i) h

/--
**FR.** Version opératorielle de `inner_singleL` : `coordL i` est LE `LinearMap.adjoint`
de `singleL i` (caractérisation par le produit scalaire, `LinearMap.eq_adjoint_iff`,
valable entre deux espaces distincts de dimension finie).

**EN.** Operator form of inner_singleL: coordL i is THE
LinearMap.adjoint of singleL i, by the inner-product characterization
LinearMap.eq_adjoint_iff, which applies between two distinct
finite-dimensional spaces.
-/
theorem adjoint_singleL (i : Fin m) :
    LinearMap.adjoint (singleL n m i) = coordL n m i := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  rw [← inner_conj_symm (coordL n m i x) y, ← inner_singleL i y x,
    inner_conj_symm x (singleL n m i y)]

/--
**FR.** Réciproque de `adjoint_singleL`, via `LinearMap.adjoint_adjoint` (pas gratuite :
appliquer `adjoint` aux deux membres de `adjoint_singleL` et involution de l'adjoint).

**EN.** Converse of adjoint_singleL, using LinearMap.adjoint_adjoint. This is
not automatic: apply adjoint to both sides of adjoint_singleL and use
involutivity of the adjoint.
-/
theorem adjoint_coordL (i : Fin m) :
    LinearMap.adjoint (coordL n m i) = singleL n m i := by
  rw [← adjoint_singleL i, LinearMap.adjoint_adjoint]

/--
**FR.** Les blocs sont deux à deux orthonormés : `coordL i ∘ singleL j = δᵢⱼ • id`.

**EN.** The blocks are pairwise orthonormal:
coordL i ∘ singleL j = δᵢⱼ • id.
-/
theorem coordL_singleL (i j : Fin m) :
    coordL n m i ∘ₗ singleL n m j = if i = j then LinearMap.id else 0 := by
  by_cases h : i = j
  · subst h
    simp only [if_true]
    apply LinearMap.ext
    intro x
    show WithLp.toLp 2 (fun k : Fin n => (singleL n m i x) (i, k)) = x
    simp only [singleL, LinearMap.coe_mk, AddHom.coe_mk]
    exact WithLp.toLp_ofLp (p := 2) x
  · simp only [if_neg h]
    apply LinearMap.ext
    intro x
    show WithLp.toLp 2 (fun k : Fin n => (singleL n m j x) (i, k)) = (0 : H n)
    simp only [singleL, LinearMap.coe_mk, AddHom.coe_mk, if_neg h]
    rfl

/--
**FR.** Projection orthogonale sur le `i`-ème bloc de `DilSpace n m`.

**EN.** Orthogonal projection onto the ith block of DilSpace n m.
-/
noncomputable def dilProj (n m : ℕ) (i : Fin m) : DilSpace n m →ₗ[ℂ] DilSpace n m :=
  singleL n m i ∘ₗ coordL n m i

theorem dilProj_isSymmetric (i : Fin m) : LinearMap.IsSymmetric (dilProj n m i) := by
  have hadj : LinearMap.adjoint (dilProj n m i) = dilProj n m i := by
    show LinearMap.adjoint (singleL n m i ∘ₗ coordL n m i) = singleL n m i ∘ₗ coordL n m i
    rw [LinearMap.adjoint_comp, adjoint_coordL, adjoint_singleL]
  intro x y
  have h := LinearMap.adjoint_inner_right (dilProj n m i) x y
  rw [hadj] at h
  exact h.symm

theorem dilProj_idempotent (i : Fin m) :
    dilProj n m i ∘ₗ dilProj n m i = dilProj n m i := by
  apply LinearMap.ext
  intro x
  show singleL n m i (coordL n m i (singleL n m i (coordL n m i x)))
    = singleL n m i (coordL n m i x)
  have h := LinearMap.congr_fun (coordL_singleL i i) (coordL n m i x)
  simp only [ite_true, LinearMap.comp_apply, LinearMap.id_apply] at h
  rw [h]

theorem dilProj_orthogonal {i j : Fin m} (h : i ≠ j) :
    dilProj n m i ∘ₗ dilProj n m j = 0 := by
  apply LinearMap.ext
  intro x
  show singleL n m i (coordL n m i (singleL n m j (coordL n m j x))) = 0
  have heq := LinearMap.congr_fun (coordL_singleL i j) (coordL n m j x)
  simp only [if_neg h, LinearMap.comp_apply, LinearMap.zero_apply] at heq
  rw [heq, map_zero]

/--
**FR.** `(dilProj i)_{i<m}` forme une mesure de projection : elle somme à l'identité
(reconstruction de `w` depuis ses blocs, `Finset.sum_ite_eq` sur la première
coordonnée de `Fin m × Fin n`).

**EN.** The family (dilProj i)_{i<m} forms a projection-valued measure: its
sum is the identity, reconstructing w from its blocks via
Finset.sum_ite_eq on the first coordinate of Fin m × Fin n.
-/
theorem dilProj_sum_eq_one : (∑ i, dilProj n m i) = LinearMap.id := by
  apply LinearMap.ext
  intro w
  rw [WithLp.ext_iff]
  funext p
  obtain ⟨a, b⟩ := p
  show ((∑ i, dilProj n m i) w).ofLp (a, b) = w.ofLp (a, b)
  rw [LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  simp only [dilProj, LinearMap.comp_apply, singleL, coordL, LinearMap.coe_mk, AddHom.coe_mk,
    WithLp.ofLp_toLp]
  rw [Finset.sum_ite_eq Finset.univ a (fun i => w.ofLp (i, b)), if_pos (Finset.mem_univ a)]

end
end QuantumFoundations
