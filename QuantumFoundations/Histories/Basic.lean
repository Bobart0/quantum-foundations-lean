import QuantumFoundations.Histories.Nonvacuity

/-!
**FR.** # K1 — Lemmes généraux courts

## Écart vs la feuille de route (à noter, pas à re-discuter) : (c) supprimé

La feuille de route prévoyait un but ouvert `projL_self_adjoint`/idempotence
« seulement si absent de la reconnaissance ». Reconnaissance A.2 : les deux
faits sont dérivables en une ligne depuis `gleason`/Mathlib, sans laisser de
but supplémentaire ouvert :
* `LinearMap.IsSymmetric (projL A)` via `Submodule.starProjection_isSymmetric`.
* `projL A (projL A x) = projL A x` via `Submodule.isIdempotentElem_starProjection`.
Aucun des deux n'est actuellement invoqué ailleurs dans ce bloc (K1(a)/K1(b) ne
s'en servent pas) ; ils seront cités inline le jour où K2/K3 en ont besoin,
plutôt que factorisés ici sans utilisateur. K1 ne compte donc que 2 buts
ouverts ((a) et (b)), pas 3.

**EN.** # K1 — Short general lemmas

## Deviation from the roadmap (to be recorded, not revisited): item (c) removed

The roadmap included an open goal for projL_self_adjoint/idempotence “only
if absent from reconnaissance.” Reconnaissance A.2 showed that both facts are
one-line consequences of gleason/Mathlib, with no additional open goal:
* LinearMap.IsSymmetric (projL A) via Submodule.starProjection_isSymmetric.
* projL A (projL A x) = projL A x via Submodule.isIdempotentElem_starProjection.
Neither fact is currently invoked elsewhere in this block (K1(a)/K1(b) do
not use them); they will be cited inline when K2/K3 requires them, rather
than factored out here without a user. K1 therefore contains only 2 open
goals, (a) and (b), not 3.
-/

namespace QuantumFoundations.Histories

open scoped InnerProductSpace
open Gleason QuantumFoundations.BornRule

noncomputable section

variable {n L : ℕ}

/--
**FR.** Le dernier étage d'une histoire est le seul à contraindre l'appartenance
de `chainOp h ψ` : la projection finale de la classe d'opérateurs (`Fin.foldl`
déroulé une fois via `Fin.foldl_succ_last`) tombe dans la cellule `h (Fin.last
L)`, quels que soient les étages antérieurs.

**EN.** Only the final stage of a history constrains membership of
chainOp h ψ: the final projection in the operator class (Fin.foldl
unfolded once via Fin.foldl_succ_last) lies in the cell
h (Fin.last
L), irrespective of the preceding stages.
-/
private theorem chainOp_mem_last (h : History n (L + 1)) (ψ : H n) :
    chainOp h ψ ∈ h (Fin.last L) := by
  show (Fin.foldl (L + 1) (fun acc t => projL (h t) ∘ₗ acc) LinearMap.id) ψ ∈ h (Fin.last L)
  rw [Fin.foldl_succ_last, LinearMap.comp_apply]
  exact Submodule.starProjection_apply_mem (h (Fin.last L)) _

/--
**FR.** **K1(a).** Si deux histoires d'une même famille `Ps : Fin (L+1) →
Perspective n` diffèrent au DERNIER étage, leur fonctionnelle de décohérence
s'annule automatiquement — sans qu'il soit besoin d'examiner les étages
antérieurs. C'est le lemme qui réduit la charge de K2 : pour `L = 1` (deux
étages, indices `0` et `1`), il ne reste à vérifier que les paires
d'histoires différant SEULEMENT à l'étage `0`.

**EN.** K1(a). If two histories from the same family
Ps : Fin (L+1) →
Perspective n differ at the FINAL stage, their
decoherence functional vanishes automatically, without any need to inspect
the preceding stages. This lemma reduces the burden in K2: for L = 1
(two stages, indexed by 0 and 1), it remains only to check pairs of
histories that differ SOLELY at stage 0.
-/
theorem decFunctional_last_stage_orthogonal (Ps : Fin (L + 1) → Perspective n) (ψ : H n)
    (h k : History n (L + 1)) (hh : IsHistoryOf Ps h) (hk : IsHistoryOf Ps k)
    (hlast : h (Fin.last L) ≠ k (Fin.last L)) :
    decFunctional ψ h k = 0 := by
  have hmem_h : chainOp h ψ ∈ h (Fin.last L) := chainOp_mem_last h ψ
  have hmem_k : chainOp k ψ ∈ k (Fin.last L) := chainOp_mem_last k ψ
  have hh_last : h (Fin.last L) ∈ (Ps (Fin.last L)).cells := hh (Fin.last L)
  have hk_last : k (Fin.last L) ∈ (Ps (Fin.last L)).cells := hk (Fin.last L)
  have hortho : h (Fin.last L) ≤ (k (Fin.last L))ᗮ :=
    (Ps (Fin.last L)).ortho (h (Fin.last L)) hh_last (k (Fin.last L)) hk_last hlast
  show ⟪chainOp k ψ, chainOp h ψ⟫_ℂ = 0
  have hperp : chainOp h ψ ∈ (k (Fin.last L))ᗮ := hortho hmem_h
  exact (Submodule.mem_orthogonal (k (Fin.last L)) (chainOp h ψ)).mp hperp (chainOp k ψ) hmem_k

/--
**FR.** **K1(b).** Version minimale de l'additivité des probabilités d'histoires
(écho d'`AxGrain`), suffisante pour K3 : sur une perspective `D1` quelconque
de l'étage final, la somme des probabilités de prolongement d'une histoire
partielle `c0` égale la probabilité de `c0` seule (théorème de Pythagore fini
sur `D1`, via `sum_sq_projL_of_pairwise_isOrtho` désormais public dans
`BornRule/Perspective.lean`).

**EN.** K1(b). Minimal form of additivity for history probabilities (echoing
AxGrain), sufficient for K3: for an arbitrary final-stage perspective D1,
the sum of the probabilities of all extensions of a partial history c0
equals the probability of c0 alone. This follows from the finite
Pythagorean theorem on D1, via sum_sq_projL_of_pairwise_isOrtho, now
public in BornRule/Perspective.lean.
-/
theorem histProb_additivity_two_stage (D1 : Perspective n) (ψ : H n)
    (c0 : Submodule ℂ (H n)) :
    ∑ c ∈ D1.cells, ‖projL c (projL c0 ψ)‖ ^ 2 = ‖projL c0 ψ‖ ^ 2 := by
  have htop : D1.cells.sup id = (⊤ : Submodule ℂ (H n)) := by
    rw [Finset.sup_id_eq_sSup]; exact D1.span
  have hpyth := sum_sq_projL_of_pairwise_isOrtho D1.cells D1.ortho (projL c0 ψ)
  rw [htop] at hpyth
  have hid : projL (⊤ : Submodule ℂ (H n)) = LinearMap.id := by
    unfold projL
    rw [Submodule.starProjection_top]
    rfl
  rw [hid] at hpyth
  simpa using hpyth.symm

end
end QuantumFoundations.Histories
