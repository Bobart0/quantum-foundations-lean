import QuantumFoundations.Complexity.RecordPersistence
import QuantumFoundations.Complexity.MinComplexity

/-!
# C7e — Transport of exact minimum circuit complexities

The minimum layer is derived only after the relational persistence
certificates.  The generic transport lemma works directly under the
`WithTop ℕ` infimum and therefore does not assume that a minimum is attained.
-/

namespace QuantumFoundations.Complexity

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

/-- If every `P`-circuit can be transformed into a `Q`-circuit at additive
cost at most `s`, then the minimum for `Q` is at most the minimum for `P`
plus `s`.  This statement does not require either infimum to be attained. -/
theorem minCircuitLength_transport_le {N d : ℕ}
    {P Q : Circuit N d → Prop}
    (F : Circuit N d → Circuit N d) (s : ℕ)
    (hPQ : ∀ C, P C → Q (F C))
    (hlen : ∀ C, Circuit.length (F C) ≤ Circuit.length C + s) :
    minCircuitLength Q ≤ minCircuitLength P + (s : WithTop ℕ) := by
  classical
  have hadd : minCircuitLength P + (s : WithTop ℕ) =
      ⨅ C, (if P C then (Circuit.length C : WithTop ℕ) else ⊤) +
        (s : WithTop ℕ) := by
    unfold minCircuitLength
    exact ENat.iInf_add
  rw [hadd]
  apply le_iInf
  intro C
  by_cases hC : P C
  · simp only [hC, if_true]
    calc
      minCircuitLength Q ≤ (Circuit.length (F C) : WithTop ℕ) :=
        minCircuitLength_le_of_witness (F C) (hPQ C hC)
      _ ≤ (Circuit.length C + s : ℕ) := by exact_mod_cast hlen C
      _ = (Circuit.length C : WithTop ℕ) + (s : WithTop ℕ) := by norm_num
  · simp [hC]

/-- Exact distinguishability complexity can increase by at most one
reversible-conjugation overhead. -/
theorem distinguishabilityComplexity_under_evolution
    (Evo : ReversibleCircuitEvolution N d)
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N)) (δ : ℝ) :
    distinguishabilityComplexity e
        (Circuit.evalOnH Evo.forward e a)
        (Circuit.evalOnH Evo.forward e b) δ
      ≤ distinguishabilityComplexity e a b δ + (Evo.overhead : WithTop ℕ) := by
  unfold distinguishabilityComplexity
  apply minCircuitLength_transport_le Evo.pushForward Evo.overhead
  · intro C hC
    exact (Evo.distinguishesAt_pushForward_iff C e a b δ).mp hC
  · intro C
    rw [Evo.pushForward_length_eq]

/-- Pulling back any evolved interference circuit shows that the initial
interference complexity is at most the evolved complexity plus one
reversible-conjugation overhead. -/
theorem interferenceComplexity_transport
    (Evo : ReversibleCircuitEvolution N d)
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N)) (δ : ℝ) :
    interferenceComplexity e a b δ
      ≤ interferenceComplexity e
          (Circuit.evalOnH Evo.forward e a)
          (Circuit.evalOnH Evo.forward e b) δ +
        (Evo.overhead : WithTop ℕ) := by
  unfold interferenceComplexity
  apply minCircuitLength_transport_le Evo.pullBack Evo.overhead
  · intro C hC
    exact (Evo.interferesAt_pullBack_iff C e a b δ).mp hC
  · intro C
    rw [Evo.pullBack_length_eq]

/-- Minimum-level proxy-gap persistence obtained from finite initial
certificates.  The physical argument remains in the relational layer; the
`WithTop ℕ` conclusion is only an order-theoretic packaging of it. -/
theorem proxy_complexity_gap_persists_of_explicit_bounds
    (Evo : ReversibleCircuitEvolution N d)
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N))
    (δ : ℝ) (B D : ℕ)
    (hI : HasInterferenceLowerBound e a b δ B)
    (hD : HasDistinguishabilityUpperBound e a b δ D)
    (g : ℕ) (hbudget : D + 2 * Evo.overhead + g ≤ B) :
    distinguishabilityComplexity e
        (Circuit.evalOnH Evo.forward e a)
        (Circuit.evalOnH Evo.forward e b) δ + (g : WithTop ℕ)
      ≤ interferenceComplexity e
        (Circuit.evalOnH Evo.forward e a)
        (Circuit.evalOnH Evo.forward e b) δ := by
  obtain ⟨B', D', hI', hD', hgap⟩ :=
    proxy_gap_persists_of_explicit_bounds Evo e a b δ B D hI hD g hbudget
  have hDmin := complexity_le_of_distinguishabilityUpperBound hD'
  have hImin := interferenceLowerBound_le_complexity hI'
  calc
    distinguishabilityComplexity e
          (Circuit.evalOnH Evo.forward e a)
          (Circuit.evalOnH Evo.forward e b) δ + (g : WithTop ℕ)
        ≤ (D' : WithTop ℕ) + (g : WithTop ℕ) := add_le_add hDmin le_rfl
    _ = (D' + g : ℕ) := by norm_num
    _ ≤ (B' : WithTop ℕ) := by exact_mod_cast hgap
    _ ≤ interferenceComplexity e
          (Circuit.evalOnH Evo.forward e a)
          (Circuit.evalOnH Evo.forward e b) δ := hImin

#print axioms distinguishabilityComplexity_under_evolution
#print axioms interferenceComplexity_transport
#print axioms proxy_complexity_gap_persists_of_explicit_bounds

end

end QuantumFoundations.Complexity
