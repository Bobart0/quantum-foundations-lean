import QuantumFoundations.Complexity.ApproxRecordDefs

/-!
# C8a — Approximate recorded pairs

Two labels are tracked symmetrically across every region: label `i` records
`a` against `b`, while label `j` records `b` against `a`.  The two aggregate
budgets remain separate because the interference expression later uses their
sum.
-/

namespace QuantumFoundations.Complexity

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

/-- Across every record region, projector `i` approximately fixes `a` and
rejects `b`, while projector `j` approximately fixes `b` and rejects `a`. -/
def ApproxRecordedPairOn {n K R : ℕ} [NeZero R]
    (recs : Fin R → LabeledResolution n K) (a b : H n) (i j : Fin K)
    (ηi ηj : ℝ) : Prop :=
  ∀ r,
    ApproxRecordFor (rproj (recs r) i) a b ηi ∧
      ApproxRecordFor (rproj (recs r) j) b a ηj

namespace ApproxRecordedPairOn

/-- Increasing either label's aggregate budget preserves an approximate
recorded pair. -/
theorem mono {n K R : ℕ} [NeZero R]
    {recs : Fin R → LabeledResolution n K} {a b : H n} {i j : Fin K}
    {ηi ηj ηi' ηj' : ℝ}
    (h : ApproxRecordedPairOn recs a b i j ηi ηj)
    (hi : ηi ≤ ηi') (hj : ηj ≤ ηj') :
    ApproxRecordedPairOn recs a b i j ηi' ηj' := by
  intro r
  exact ⟨(h r).1.mono hi, (h r).2.mono hj⟩

end ApproxRecordedPairOn

/-- Exact redundant records instantiate the approximate-pair API with zero
error on the two nonzero normalized branches. -/
theorem exact_records_give_approxRecordedPairOn_zero
    {n K R : ℕ} [NeZero R]
    (recs : Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : IsRecordedOn ψ recs) (i j : Fin K) (hij : i ≠ j)
    (_hi : branch recs ψ i ≠ 0) (_hj : branch recs ψ j ≠ 0) :
    ApproxRecordedPairOn recs
      (normalizedBranch recs ψ i) (normalizedBranch recs ψ j) i j 0 0 := by
  intro r
  constructor
  · apply approxRecordFor_zero_of_fixes_rejects
    · exact recordProj_normalizedBranch_same recs ψ hrec r i
    · exact recordProj_normalizedBranch_other recs ψ hrec r j i hij.symm
  · apply approxRecordFor_zero_of_fixes_rejects
    · exact recordProj_normalizedBranch_same recs ψ hrec r j
    · exact recordProj_normalizedBranch_other recs ψ hrec r i j hij

end


end QuantumFoundations.Complexity
