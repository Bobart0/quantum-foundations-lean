import QuantumFoundations.Naimark.BinaryImpl.Minimal
import QuantumFoundations.Naimark.BinaryImpl.GramRange

/-!
**FR.** # Unicité stricte des implémentations minimales

Théorème central du Module C : `minimal_strictIso` — deux implémentations
MINIMALES d'un même effet sont TOUJOURS strictement isomorphes.

**Choix d'architecture (remplace la construction générale "somme
orthogonale d'isométries" initialement envisagée).** Plutôt que de
construire séparément `eventGeneratedEquiv`/`complementGeneratedEquiv`
(`GramRange.lean`) puis de les recoller en une isométrie du sous-espace
minimal via une machinerie générale de somme orthogonale, ce fichier
route directement par UNE application unique du lemme général de
`GramRange.lean`, appliquée à l'application combinée

  `combinedLeg I : DilSpace n 2 →ₗ[ℂ] EuclideanSpace ℂ ι`
  `combinedLeg I w := eventLeg I (coordL 0 w) + complementLeg I (coordL 1 w)`

dont l'image est exactement `minimalSubspace I` (`range_combinedLeg`), et
dont le Gram `adjoint (combinedLeg I) ∘ combinedLeg I` ne dépend que de `E`
(`combinedLeg_gram_eq`), pas de l'implémentation `I` choisie. Sous
minimalité, `combinedLeg I` est SURJECTIVE, ce qui permet d'invoquer la
variante ambiante-à-ambiante `exists_isometryEquiv_of_adjoint_comp_self_eq_of_surjective`
(`GramRange.lean`) et d'obtenir directement une isométrie de
`EuclideanSpace ℂ ι` tout entier vers `EuclideanSpace ℂ κ`, sans jamais
manipuler de sous-type `↥(minimalSubspace I)` -- ce qui a permis d'éviter
un diamant d'instances Lean persistant entre le chemin `Module` propre à
`EuclideanSpace`/`WithLp` et celui, générique, attendu par
`LinearIsometryEquiv.inner_map_map`/`LinearEquiv.isometryOfInner` lorsqu'ils
sont invoqués à un type `Submodule ℂ (EuclideanSpace ℂ ι)` explicite.

**EN.** # Strict uniqueness of minimal implementations

Central theorem of Module C: `minimal_strictIso` -- two MINIMAL
implementations of the same effect are ALWAYS strictly isomorphic.

**Architecture choice (replaces the general "orthogonal sum of
isometries" construction originally planned).** Rather than separately
building `eventGeneratedEquiv`/`complementGeneratedEquiv`
(`GramRange.lean`) and gluing them into an isometry of the minimal
subspace via a general orthogonal-sum machinery, this file routes through
a SINGLE application of `GramRange.lean`'s general lemma, applied to the
combined map

  `combinedLeg I : DilSpace n 2 →ₗ[ℂ] EuclideanSpace ℂ ι`
  `combinedLeg I w := eventLeg I (coordL 0 w) + complementLeg I (coordL 1 w)`

whose image is exactly `minimalSubspace I` (`range_combinedLeg`), and
whose Gram matrix `adjoint (combinedLeg I) ∘ combinedLeg I` depends only on
`E` (`combinedLeg_gram_eq`), not on the chosen implementation `I`. Under
minimality, `combinedLeg I` is SURJECTIVE, which lets us invoke the
ambient-to-ambient variant
`exists_isometryEquiv_of_adjoint_comp_self_eq_of_surjective`
(`GramRange.lean`) and obtain directly an isometry of the WHOLE
`EuclideanSpace ℂ ι` onto `EuclideanSpace ℂ κ`, without ever handling a
`↥(minimalSubspace I)` subtype -- avoiding a persistent Lean instance
diamond between `EuclideanSpace`/`WithLp`'s own `Module` path and the
generic one expected by `LinearIsometryEquiv.inner_map_map`/
`LinearEquiv.isometryOfInner` when invoked at an explicit
`Submodule ℂ (EuclideanSpace ℂ ι)` type.
-/

namespace QuantumFoundations.Naimark.BinaryImpl

open QuantumFoundations Gleason
open scoped InnerProductSpace

noncomputable section

variable {n : ℕ} {E : H n →ₗ[ℂ] H n} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The combined leg map, indexed by the 2-block dilation space
`DilSpace n 2` (reusing `singleL`/`coordL` from `Naimark/DilSpace.lean`):
`w ↦ eventLeg I (coordL 0 w) + complementLeg I (coordL 1 w)`. Its range is
exactly `minimalSubspace I`. -/
def combinedLeg (I : BinaryImpl n E ι) : DilSpace n 2 →ₗ[ℂ] EuclideanSpace ℂ ι :=
  eventLeg I ∘ₗ coordL n 2 0 + complementLeg I ∘ₗ coordL n 2 1

theorem combinedLeg_apply (I : BinaryImpl n E ι) (w : DilSpace n 2) :
    combinedLeg I w = eventLeg I (coordL n 2 0 w) + complementLeg I (coordL n 2 1 w) := rfl

theorem range_combinedLeg (I : BinaryImpl n E ι) :
    LinearMap.range (combinedLeg I) = minimalSubspace I := by
  apply le_antisymm
  · rintro y ⟨w, rfl⟩
    rw [combinedLeg_apply]
    exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨_, rfl⟩) (Submodule.mem_sup_right ⟨_, rfl⟩)
  · rw [minimalSubspace, sup_le_iff]
    constructor
    · rintro y ⟨x1, rfl⟩
      refine ⟨singleL n 2 0 x1, ?_⟩
      rw [combinedLeg_apply]
      have h0 := LinearMap.congr_fun (coordL_singleL (n := n) (m := 2) 0 0) x1
      have h1 := LinearMap.congr_fun (coordL_singleL (n := n) (m := 2) 1 0) x1
      simp only [LinearMap.comp_apply] at h0 h1
      simp at h0 h1
      rw [h0, h1, map_zero, add_zero]
    · rintro y ⟨x2, rfl⟩
      refine ⟨singleL n 2 1 x2, ?_⟩
      rw [combinedLeg_apply]
      have h0 := LinearMap.congr_fun (coordL_singleL (n := n) (m := 2) 0 1) x2
      have h1 := LinearMap.congr_fun (coordL_singleL (n := n) (m := 2) 1 1) x2
      simp only [LinearMap.comp_apply] at h0 h1
      simp at h0 h1
      rw [h0, h1, map_zero, zero_add]

private theorem cross_gram_zero (I : BinaryImpl n E ι) (a b : H n) :
    ⟪eventLeg I a, complementLeg I b⟫_ℂ = 0 := by
  rw [← LinearMap.adjoint_inner_right (eventLeg I) a (complementLeg I b)]
  have h := LinearMap.congr_fun (event_complement_cross_gram_eq_zero I) b
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
  rw [h, inner_zero_right]

private theorem cross_gram_zero' (I : BinaryImpl n E ι) (a b : H n) :
    ⟪complementLeg I a, eventLeg I b⟫_ℂ = 0 := by
  have h := cross_gram_zero I b a
  rw [← inner_conj_symm] at h
  simpa using congrArg (starRingEnd ℂ) h

private theorem inner_eventLeg (I : BinaryImpl n E ι) (a b : H n) :
    ⟪eventLeg I a, eventLeg I b⟫_ℂ = ⟪a, E b⟫_ℂ := by
  rw [← LinearMap.adjoint_inner_right (eventLeg I) a (eventLeg I b)]
  have h := LinearMap.congr_fun (eventLeg_adjoint_comp_self I) b
  simp only [LinearMap.comp_apply] at h
  rw [h]

private theorem inner_complementLeg (I : BinaryImpl n E ι) (a b : H n) :
    ⟪complementLeg I a, complementLeg I b⟫_ℂ = ⟪a, (1 - E) b⟫_ℂ := by
  rw [← LinearMap.adjoint_inner_right (complementLeg I) a (complementLeg I b)]
  have h := LinearMap.congr_fun (complementLeg_adjoint_comp_self I) b
  simp only [LinearMap.comp_apply] at h
  rw [h]

/-- The key fact making `minimal_strictIso` possible: the Gram matrix of
`combinedLeg I` depends only on `E`, not on `I`. -/
theorem combinedLeg_gram_eq (I : BinaryImpl n E ι) (J : BinaryImpl n E κ) :
    LinearMap.adjoint (combinedLeg I) ∘ₗ combinedLeg I
      = LinearMap.adjoint (combinedLeg J) ∘ₗ combinedLeg J := by
  apply LinearMap.ext
  intro w
  apply ext_inner_left ℂ
  intro w'
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  rw [combinedLeg_apply, combinedLeg_apply, combinedLeg_apply, combinedLeg_apply]
  simp only [inner_add_left, inner_add_right]
  rw [cross_gram_zero I (coordL n 2 0 w') (coordL n 2 1 w), cross_gram_zero' I (coordL n 2 1 w') (coordL n 2 0 w),
    cross_gram_zero J (coordL n 2 0 w') (coordL n 2 1 w), cross_gram_zero' J (coordL n 2 1 w') (coordL n 2 0 w),
    inner_eventLeg I (coordL n 2 0 w') (coordL n 2 0 w), inner_complementLeg I (coordL n 2 1 w') (coordL n 2 1 w),
    inner_eventLeg J (coordL n 2 0 w') (coordL n 2 0 w), inner_complementLeg J (coordL n 2 1 w') (coordL n 2 1 w)]

/-- The doubled witness `singleL 0 x + singleL 1 x`, whose `combinedLeg`
value is exactly the ambient encoding `I.encoding x`. -/
private theorem combinedLeg_doubled (I : BinaryImpl n E ι) (x : H n) :
    combinedLeg I (singleL n 2 0 x + singleL n 2 1 x) = I.encoding x := by
  rw [combinedLeg_apply]
  simp only [map_add]
  have h00 := LinearMap.congr_fun (coordL_singleL (n := n) (m := 2) 0 0) x
  have h01 := LinearMap.congr_fun (coordL_singleL (n := n) (m := 2) 0 1) x
  have h10 := LinearMap.congr_fun (coordL_singleL (n := n) (m := 2) 1 0) x
  have h11 := LinearMap.congr_fun (coordL_singleL (n := n) (m := 2) 1 1) x
  simp only [LinearMap.comp_apply] at h00 h01 h10 h11
  simp at h00 h01 h10 h11
  rw [h00, h01, h10, h11]
  simp only [map_zero, add_zero, zero_add]
  have h := LinearMap.congr_fun I.cell_add_complement_eq_one (I.encoding x)
  simpa [eventLeg, complementLeg] using h

/-- `I.cell` applied to a `combinedLeg` value collapses to the
event-side-only witness `singleL 0 (coordL 0 w)`. -/
private theorem cell_combinedLeg {ι : Type} [Fintype ι] [DecidableEq ι] (I : BinaryImpl n E ι)
    (w : DilSpace n 2) :
    I.cell (combinedLeg I w) = combinedLeg I (singleL n 2 0 (coordL n 2 0 w)) := by
  rw [combinedLeg_apply, combinedLeg_apply]
  have h0 := LinearMap.congr_fun (coordL_singleL (n := n) (m := 2) 0 0) (coordL n 2 0 w)
  have h1 := LinearMap.congr_fun (coordL_singleL (n := n) (m := 2) 1 0) (coordL n 2 0 w)
  simp only [LinearMap.comp_apply] at h0 h1
  simp at h0 h1
  rw [h0, h1, map_zero, add_zero, map_add]
  have ha : I.cell (eventLeg I (coordL n 2 0 w)) = eventLeg I (coordL n 2 0 w) := by
    show I.cell (I.cell (I.encoding (coordL n 2 0 w))) = I.cell (I.encoding (coordL n 2 0 w))
    have h := LinearMap.congr_fun I.cell_idempotent (I.encoding (coordL n 2 0 w))
    simpa using h
  have hb : I.cell (complementLeg I (coordL n 2 1 w)) = 0 := by
    show I.cell (I.complementCell (I.encoding (coordL n 2 1 w))) = 0
    have h := LinearMap.congr_fun I.cell_comp_complement_eq_zero (I.encoding (coordL n 2 1 w))
    simpa using h
  rw [ha, hb, add_zero]

/-- **Minimal uniqueness.** Two MINIMAL implementations of the same effect
are strictly isomorphic. The witness isometry is built from a single
application of `exists_isometryEquiv_of_adjoint_comp_self_eq_of_surjective`
to `combinedLeg I`/`combinedLeg J`, both surjective under minimality
(`IsMinimal` unfolds exactly to `range (combinedLeg _) = ⊤`, via
`range_combinedLeg`). -/
theorem minimal_strictIso {I : BinaryImpl n E ι} {J : BinaryImpl n E κ}
    (hI : IsMinimal I) (hJ : IsMinimal J) : BinaryImpl.StrictIso I J := by
  have hIsurj : Function.Surjective (combinedLeg I) := by
    rw [← LinearMap.range_eq_top, range_combinedLeg]; exact hI
  have hJsurj : Function.Surjective (combinedLeg J) := by
    rw [← LinearMap.range_eq_top, range_combinedLeg]; exact hJ
  obtain ⟨U, hU⟩ := exists_isometryEquiv_of_adjoint_comp_self_eq_of_surjective (combinedLeg I) (combinedLeg J)
    (combinedLeg_gram_eq I J) hIsurj hJsurj
  refine ⟨U, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    show U (I.encoding x) = J.encoding x
    rw [← combinedLeg_doubled I x, hU, combinedLeg_doubled J x]
  · apply LinearMap.ext
    intro y
    show U (I.cell y) = J.cell (U y)
    obtain ⟨w, hw⟩ := hIsurj y
    rw [← hw, cell_combinedLeg I w, hU (singleL n 2 0 (coordL n 2 0 w)), hU w, ← cell_combinedLeg J w]

end

end QuantumFoundations.Naimark.BinaryImpl
