import QuantumFoundations.Naimark.SqrtOp
import QuantumFoundations.Naimark.DilSpace

/-!
# Dilatation de Naimark (Watrous, *TQI*, Theorem 2.42)

`dilV P := Σᵢ singleL i ∘ √(E i)` réalise la POVM `P` comme mesure projective sur
`DilSpace n m` : `dilV` est une isométrie, et `adjoint (dilV P) ∘ dilProj i ∘ dilV P = E i`.
-/

namespace QuantumFoundations

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n m : ℕ}

/-- L'isométrie de dilatation de Naimark : `V := Σᵢ singleL i ∘ √(E i)`. -/
noncomputable def dilV (P : POVM n m) : H n →ₗ[ℂ] DilSpace n m :=
  ∑ i, singleL n m i ∘ₗ sqrtOp (P.E i)

/-- **Pivot 1.** `coordL i` récupère `√(E i)` depuis `dilV P` : une seule somme sur
l'indice de bloc, effondrée par `coordL_singleL` (N2) — jamais de double somme
(cf. CLAUDE.md règle 7 / leçon `riesz_rep_assembly`). -/
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

/-- **Pivot 2.** `singleL i` "retrouve" `√(E i)` via l'adjoint de `dilV P` : adjoint
d'une somme finie (`map_sum`) + `adjoint_comp` (ordre inversé) + symétrie de
`sqrtOp (E i)` (N1) + `adjoint_singleL` (N2), puis une seule somme sur l'indice de
bloc effondrée par `coordL_singleL`. -/
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

/-- `dilV P` est une isométrie : `adjoint (dilV P) ∘ dilV P = id`. -/
theorem dilV_isometry (P : POVM n m) :
    LinearMap.adjoint (dilV P) ∘ₗ dilV P = LinearMap.id := by
  sorry

/-- La mesure projective `dilProj` réalise `P` via `dilV` : `adjoint V ∘ dilProj i ∘ V = E i`. -/
theorem naimark_dilation (P : POVM n m) (i : Fin m) :
    LinearMap.adjoint (dilV P) ∘ₗ dilProj n m i ∘ₗ dilV P = P.E i := by
  sorry

/-- **Théorème de dilation de Naimark** (dimension finie, somme directe). -/
theorem naimark (P : POVM n m) :
    ∃ V : H n →ₗ[ℂ] DilSpace n m, LinearMap.adjoint V ∘ₗ V = LinearMap.id ∧
      ∀ i, LinearMap.adjoint V ∘ₗ dilProj n m i ∘ₗ V = P.E i := by
  sorry

/-- Corollaire statistique : les probabilités de Born coïncident sous la dilatation. -/
theorem naimark_born (P : POVM n m) (i : Fin m) (x : H n) :
    ⟪x, P.E i x⟫_ℂ = ⟪dilV P x, dilProj n m i (dilV P x)⟫_ℂ := by
  sorry

end
end QuantumFoundations
