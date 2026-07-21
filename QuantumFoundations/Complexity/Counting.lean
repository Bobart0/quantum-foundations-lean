import Mathlib.Data.Fintype.Card

/-!
# C2 — Finite counting for disjoint regions

This file is independent of Hilbert spaces.  It packages the only
combinatorial fact needed by the circuit lower bound: pairwise disjoint
regions that all meet one finite support inject into that support.
-/

namespace QuantumFoundations.Complexity

/--
If a finite indexed family of pairwise disjoint finite regions all meet a
finite support, then the number of regions is at most the support cardinality.
-/
theorem regions_card_le_support_card {ι α : Type*} [Fintype ι] [DecidableEq α]
    (regions : ι → Finset α) (support : Finset α)
    (hpairwise : ∀ i j, i ≠ j → Disjoint (regions i) (regions j))
    (htouched : ∀ i, ¬ Disjoint support (regions i)) :
    Fintype.card ι ≤ support.card := by
  classical
  choose site hsite_support hsite_region using fun i =>
    Finset.not_disjoint_iff.mp (htouched i)
  let touchedSite : ι → {x // x ∈ support} :=
    fun i => ⟨site i, hsite_support i⟩
  have hinjective : Function.Injective touchedSite := by
    intro i j hij
    by_contra hne
    have hdisj := Finset.disjoint_left.mp (hpairwise i j hne)
    have hsite_eq : site i = site j := congrArg Subtype.val hij
    exact hdisj (hsite_region i) (hsite_eq ▸ hsite_region j)
  simpa using Fintype.card_le_of_injective touchedSite hinjective

end QuantumFoundations.Complexity
