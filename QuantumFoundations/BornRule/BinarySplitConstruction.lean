import QuantumFoundations.BornRule.BinaryGeneratedRefinement

/-!
# Constructing a binary split of one perspective cell

This is the geometric primitive used by the finite split-generation proof.
Given a cell `q = a ⊔ b` with nonzero orthogonal children, replace `q` by
`a,b` and keep every other cell unchanged.
-/

namespace QuantumFoundations.BornRule

open scoped Classical InnerProductSpace

noncomputable section

variable {n : ℕ}

namespace Perspective

/-- Replace a cell `q` by two nonzero orthogonal subspaces `a,b` whose supremum
is exactly `q`. -/
noncomputable def splitCell
    (D : Perspective n)
    (q a b : Submodule ℂ (H n))
    (hq : q ∈ D.cells)
    (ha : a ≠ ⊥) (hb : b ≠ ⊥)
    (hab : a ≤ bᗮ)
    (hsup : a ⊔ b = q) : Perspective n := by
  have haQ : a ≤ q := by rw [← hsup]; exact le_sup_left
  have hbQ : b ≤ q := by rw [← hsup]; exact le_sup_right
  have hba : b ≤ aᗮ :=
    (Submodule.le_orthogonal_orthogonal b).trans (Submodule.orthogonal_le hab)
  exact
  { cells := D.cells.erase q ∪ {a, b}
    nz := by
      intro c hc
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with hcOld | hca | hcb
      · exact D.nz c (Finset.mem_of_mem_erase hcOld)
      · simpa [hca] using ha
      · simpa [hcb] using hb
    ortho := by
      intro c hc c' hc' hne
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hc hc'
      rcases hc with hcOld | hca | hcb <;>
        rcases hc' with hcOld' | hca' | hcb'
      · exact D.ortho c (Finset.mem_of_mem_erase hcOld)
          c' (Finset.mem_of_mem_erase hcOld') hne
      · subst c'
        have hcD : c ∈ D.cells := Finset.mem_of_mem_erase hcOld
        have hcq : c ≠ q := (Finset.mem_erase.mp hcOld).1
        exact (D.ortho c hcD q hq hcq).trans (Submodule.orthogonal_le haQ)
      · subst c'
        have hcD : c ∈ D.cells := Finset.mem_of_mem_erase hcOld
        have hcq : c ≠ q := (Finset.mem_erase.mp hcOld).1
        exact (D.ortho c hcD q hq hcq).trans (Submodule.orthogonal_le hbQ)
      · subst c
        have hc'D : c' ∈ D.cells := Finset.mem_of_mem_erase hcOld'
        have hc'q : c' ≠ q := (Finset.mem_erase.mp hcOld').1
        exact haQ.trans (D.ortho q hq c' hc'D (Ne.symm hc'q))
      · exact absurd rfl hne
      · subst c; subst c'; exact hab
      · subst c
        have hc'D : c' ∈ D.cells := Finset.mem_of_mem_erase hcOld'
        have hc'q : c' ≠ q := (Finset.mem_erase.mp hcOld').1
        exact hbQ.trans (D.ortho q hq c' hc'D (Ne.symm hc'q))
      · subst c; subst c'; exact hba
      · exact absurd rfl hne
    span := by
      apply le_antisymm le_top
      rw [← D.span]
      apply sSup_le
      intro c hcD
      simp only [Finset.mem_coe] at hcD
      by_cases hcq : c = q
      · subst c
        rw [← hsup]
        apply sup_le
        · rw [← sSup_singleton a]
          apply sSup_le_sSup
          intro x hx
          simp only [Set.mem_singleton_iff] at hx
          subst x
          simp only [Finset.mem_coe]
          exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
        · rw [← sSup_singleton b]
          apply sSup_le_sSup
          intro x hx
          simp only [Set.mem_singleton_iff] at hx
          subst x
          simp only [Finset.mem_coe]
          exact Finset.mem_union_right _
            (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      · rw [← sSup_singleton c]
        apply sSup_le_sSup
        intro x hx
        simp only [Set.mem_singleton_iff] at hx
        subst x
        simp only [Finset.mem_coe]
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hcq, hcD⟩) }

private theorem splitCell_aux
    (D : Perspective n)
    (q a b : Submodule ℂ (H n))
    (hq : q ∈ D.cells)
    (ha : a ≠ ⊥) (hb : b ≠ ⊥)
    (hab : a ≤ bᗮ)
    (hsup : a ⊔ b = q) :
    let S := splitCell D q a b hq ha hb hab hsup
    q ∉ S.cells ∧
    a ≠ b ∧
    S.cells.filter (· ≤ q) = {a, b} := by
  let S := splitCell D q a b hq ha hb hab hsup
  have haQ : a ≤ q := by rw [← hsup]; exact le_sup_left
  have hbQ : b ≤ q := by rw [← hsup]; exact le_sup_right
  have hba : b ≤ aᗮ :=
    (Submodule.le_orthogonal_orthogonal b).trans (Submodule.orthogonal_le hab)
  have hq_ne_a : q ≠ a := by
    intro hqa
    apply hb
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hxa : x ∈ a := by
      have : b ≤ a := by simpa [hqa] using hbQ
      exact this hx
    have hxperp : x ∈ aᗮ := hba hx
    have hz : ⟪x, x⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal a x).mp hxperp x hxa
    exact inner_self_eq_zero.mp hz
  have hq_ne_b : q ≠ b := by
    intro hqb
    apply ha
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hxb : x ∈ b := by
      have : a ≤ b := by simpa [hqb] using haQ
      exact this hx
    have hxperp : x ∈ bᗮ := hab hx
    have hz : ⟪x, x⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal b x).mp hxperp x hxb
    exact inner_self_eq_zero.mp hz
  have hab_ne : a ≠ b := by
    intro heq
    apply hq_ne_a
    rw [← hsup, heq, sup_idem]
  have hq_not : q ∉ S.cells := by
    change q ∉ D.cells.erase q ∪ {a, b}
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact ⟨by simp, hq_ne_a, hq_ne_b⟩
  refine ⟨hq_not, hab_ne, ?_⟩
  ext c
  change c ∈ (D.cells.erase q ∪ {a, b}).filter (· ≤ q) ↔ c ∈ {a, b}
  simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hcOld | hca | hcb, hcle⟩
    · have hcD : c ∈ D.cells := (Finset.mem_erase.mp hcOld).2
      have hcq : c ≠ q := (Finset.mem_erase.mp hcOld).1
      have hceq : c = q :=
        D.unique_parent hcD hq (D.nz c hcD) (le_refl c) hcle
      exact (hcq hceq).elim
    · exact Or.inl hca
    · exact Or.inr hcb
  · intro hc
    rcases hc with rfl | rfl
    · exact ⟨Or.inr (Or.inl rfl), haQ⟩
    · exact ⟨Or.inr (Or.inr rfl), hbQ⟩

/-- The explicit cell replacement is an elementary binary split in the sense
used by `AxSplitRC`. -/
theorem splitCell_isBinarySplit
    (D : Perspective n)
    (q a b : Submodule ℂ (H n))
    (hq : q ∈ D.cells)
    (ha : a ≠ ⊥) (hb : b ≠ ⊥)
    (hab : a ≤ bᗮ)
    (hsup : a ⊔ b = q) :
    IsBinarySplit (splitCell D q a b hq ha hb hab hsup) D := by
  let S := splitCell D q a b hq ha hb hab hsup
  have haux := splitCell_aux D q a b hq ha hb hab hsup
  dsimp only at haux
  rcases haux with ⟨hqNot, hab_ne, hfilter⟩
  refine ⟨?_, q, hq, hqNot, ?_, ?_⟩
  · intro c hcS
    change c ∈ D.cells.erase q ∪ {a, b} at hcS
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hcS
    rcases hcS with hcOld | hca | hcb
    · have hcD : c ∈ D.cells := Finset.mem_of_mem_erase hcOld
      exact ⟨c, hcD, le_refl c⟩
    · subst c
      refine ⟨q, hq, ?_⟩
      rw [← hsup]
      exact le_sup_left
    · subst c
      refine ⟨q, hq, ?_⟩
      rw [← hsup]
      exact le_sup_right
  · intro c hcD hcq
    change c ∈ D.cells.erase q ∪ {a, b}
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hcq, hcD⟩)
  · rw [hfilter]
    simp [hab_ne]

end Perspective

end

end QuantumFoundations.BornRule
