import QuantumFoundations.Naimark.SqrtOp
import QuantumFoundations.Naimark.DilSpace

/-!
**FR.** # Dilatation de Naimark (Watrous, *TQI*, Theorem 2.42)

`dilV P := Σᵢ singleL i ∘ √(E i)` réalise la POVM `P` comme mesure projective sur
`DilSpace n m` : `dilV` est une isométrie, et `adjoint (dilV P) ∘ dilProj i ∘ dilV P = E i`.

**EN.** # Naimark dilation (Watrous, TQI, Theorem 2.42)

dilV P := Σᵢ singleL i ∘ √(E i) realizes the POVM P as a
projection-valued measure on DilSpace n m: dilV is an isometry, and
adjoint (dilV P) ∘ dilProj i ∘ dilV P = E i.
-/

namespace QuantumFoundations

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n m : ℕ}

/--
**FR.** L'isométrie de dilatation de Naimark : `V := Σᵢ singleL i ∘ √(E i)`.

**EN.** The Naimark dilation isometry: V := Σᵢ singleL i ∘ √(E i).
-/
noncomputable def dilV (P : POVM n m) : H n →ₗ[ℂ] DilSpace n m :=
  ∑ i, singleL n m i ∘ₗ sqrtOp (P.E i)

/--
**FR.** **Pivot 1.** `coordL i` récupère `√(E i)` depuis `dilV P` : une seule somme sur
l'indice de bloc, effondrée par `coordL_singleL` (N2) — jamais de double somme
(voir la leçon `riesz_rep_assembly` dans `docs/IMPLEMENTATION_NOTES.md`).

**EN.** Pivot 1. coordL i recovers √(E i) from dilV P: a single sum
over the block index, collapsed by coordL_singleL (N2), never a double sum
(see the riesz_rep_assembly lesson in docs/IMPLEMENTATION_NOTES.md).
-/
private theorem key1 (P : POVM n m) (i : Fin m) :
    coordL n m i ∘ₗ dilV P = sqrtOp (P.E i) := by
  apply LinearMap.ext
  intro x
  show (coordL n m i) ((∑ j, singleL n m j ∘ₗ sqrtOp (P.E j)) x) = sqrtOp (P.E i) x
  rw [LinearMap.sum_apply, map_sum]
  simp only [LinearMap.comp_apply]
  have step : ∀ j : Fin m, (coordL n m i) ((singleL n m j) (sqrtOp (P.E j) x))
      = if i = j then sqrtOp (P.E j) x else 0 := by
    intro j
    rw [← LinearMap.comp_apply, coordL_singleL i j]
    by_cases h : i = j <;> simp [h]
  simp only [step]
  rw [Finset.sum_ite_eq Finset.univ i (fun j => sqrtOp (P.E j) x), if_pos (Finset.mem_univ i)]

/--
**FR.** **Pivot 2.** `singleL i` "retrouve" `√(E i)` via l'adjoint de `dilV P` : adjoint
d'une somme finie (`map_sum`) + `adjoint_comp` (ordre inversé) + symétrie de
`sqrtOp (E i)` (N1) + `adjoint_singleL` (N2), puis une seule somme sur l'indice de
bloc effondrée par `coordL_singleL`.

**EN.** Pivot 2. singleL i “recovers” √(E i) through the adjoint of
dilV P: the adjoint of a finite sum (map_sum) + adjoint_comp (reversed
order) + symmetry of sqrtOp (E i) (N1) + adjoint_singleL (N2), followed
by a single sum over the block index collapsed by coordL_singleL.
-/
private theorem key2 (P : POVM n m) (i : Fin m) :
    LinearMap.adjoint (dilV P) ∘ₗ singleL n m i = sqrtOp (P.E i) := by
  have hadj : LinearMap.adjoint (dilV P) = ∑ j, sqrtOp (P.E j) ∘ₗ coordL n m j := by
    show LinearMap.adjoint (∑ j, singleL n m j ∘ₗ sqrtOp (P.E j)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [LinearMap.adjoint_comp, adjoint_singleL]
    congr 1
    exact (sqrtOp_isPositive (P.pos j)).1.adjoint_eq
  apply LinearMap.ext
  intro x
  show (LinearMap.adjoint (dilV P)) (singleL n m i x) = sqrtOp (P.E i) x
  rw [hadj, LinearMap.sum_apply]
  have step : ∀ j : Fin m, (sqrtOp (P.E j) ∘ₗ coordL n m j) (singleL n m i x)
      = if j = i then sqrtOp (P.E j) x else 0 := by
    intro j
    have hx := LinearMap.congr_fun (coordL_singleL j i) x
    rw [LinearMap.comp_apply] at hx
    rw [LinearMap.comp_apply, hx]
    by_cases h : j = i <;> simp [h]
  simp only [step]
  rw [Finset.sum_ite_eq' Finset.univ i (fun j => sqrtOp (P.E j) x), if_pos (Finset.mem_univ i)]

/--
**FR.** `dilV P` est une isométrie : `adjoint (dilV P) ∘ dilV P = id`. Une seule somme
sur l'indice de bloc (via `key2` puis `sqrtOp_mul_self`), jamais de double somme.

**EN.** dilV P is an isometry:
adjoint (dilV P) ∘ dilV P = id. Only one sum over the block index is used
(via key2 and then sqrtOp_mul_self), never a double sum.
-/
theorem dilV_isometry (P : POVM n m) :
    LinearMap.adjoint (dilV P) ∘ₗ dilV P = LinearMap.id := by
  apply LinearMap.ext
  intro x
  show (LinearMap.adjoint (dilV P)) ((∑ i, singleL n m i ∘ₗ sqrtOp (P.E i)) x) = x
  rw [LinearMap.sum_apply, map_sum]
  simp only [LinearMap.comp_apply]
  have step : ∀ i : Fin m, (LinearMap.adjoint (dilV P)) ((singleL n m i) (sqrtOp (P.E i) x))
      = P.E i x := by
    intro i
    rw [← LinearMap.comp_apply, key2 P i, ← LinearMap.comp_apply, sqrtOp_mul_self (P.pos i)]
  simp only [step]
  rw [← LinearMap.sum_apply, P.sum_eq_one]
  rfl

/--
**FR.** La mesure projective `dilProj` réalise `P` via `dilV` : `adjoint V ∘ dilProj i ∘ V = E i`.
Aucune somme à développer — tout vient de `key1`/`key2` déjà fermés.

**EN.** The projection-valued measure dilProj realizes P through dilV:
adjoint V ∘ dilProj i ∘ V = E i. No sum needs to be expanded; the result
follows entirely from the already established key1/key2.
-/
theorem naimark_dilation (P : POVM n m) (i : Fin m) :
    LinearMap.adjoint (dilV P) ∘ₗ dilProj n m i ∘ₗ dilV P = P.E i := by
  apply LinearMap.ext
  intro x
  show (LinearMap.adjoint (dilV P)) ((dilProj n m i) (dilV P x)) = P.E i x
  show (LinearMap.adjoint (dilV P)) ((singleL n m i) ((coordL n m i) (dilV P x))) = P.E i x
  rw [← LinearMap.comp_apply (coordL n m i) (dilV P), key1,
    ← LinearMap.comp_apply (LinearMap.adjoint (dilV P)) (singleL n m i), key2,
    ← LinearMap.comp_apply (sqrtOp (P.E i)) (sqrtOp (P.E i)), sqrtOp_mul_self (P.pos i)]

/--
**FR.** **Théorème de dilation de Naimark** (dimension finie, somme directe).

**EN.** Naimark dilation theorem (finite-dimensional, direct-sum form).
-/
theorem naimark (P : POVM n m) :
    ∃ V : H n →ₗ[ℂ] DilSpace n m, LinearMap.adjoint V ∘ₗ V = LinearMap.id ∧
      ∀ i, LinearMap.adjoint V ∘ₗ dilProj n m i ∘ₗ V = P.E i :=
  ⟨dilV P, dilV_isometry P, naimark_dilation P⟩

/--
**FR.** Corollaire statistique : les probabilités de Born coïncident sous la dilatation.

**EN.** Statistical corollary: Born probabilities are preserved under the dilation.
-/
theorem naimark_born (P : POVM n m) (i : Fin m) (x : H n) :
    ⟪x, P.E i x⟫_ℂ = ⟪dilV P x, dilProj n m i (dilV P x)⟫_ℂ := by
  rw [← LinearMap.adjoint_inner_right (dilV P) x (dilProj n m i (dilV P x))]
  have h := LinearMap.congr_fun (naimark_dilation P i) x
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
  rw [h]

end
end QuantumFoundations
