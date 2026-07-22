import QuantumFoundations.Complexity.CircuitInverse
import QuantumFoundations.Complexity.Models.Repetition.States

/-!
# C11a — Controlled bit-flip gates

An explicit two-site `TwoLocalGate` on qubit sites: the `target` bit is
XORed by the `control` bit, and every other site (including `control`
itself) is left unchanged.  The underlying permutation of computational-
basis configurations,

    `controlledBitFlipMap control target g := Function.update g target
      (g target + g control)`,

is an involution whenever `control ≠ target` (applying it twice adds
`g control` to the target bit twice, and `x + x = 0` in `Fin 2`).  This
mirrors the single-site `bitFlipUnitary`/`bitFlipGate` construction in the
repetition model's `Interference.lean`, generalized from a one-site swap to
a two-site controlled swap: the local kernel witnessing `IsLocalTo` now
depends on the restriction of both configurations to `{control, target}`
rather than to a single site.
-/

namespace QuantumFoundations.Complexity.Gates

open scoped InnerProductSpace Classical

open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.RepetitionModel

noncomputable section

variable {N : ℕ}

/-- Flip the `target` bit by XOR with the `control` bit (`Fin 2` addition is
addition mod `2`, i.e. XOR); every other site, including `control`, is
unchanged. -/
def controlledBitFlipMap (control target : Fin N) (g : Fin N → Fin 2) : Fin N → Fin 2 :=
  Function.update g target (g target + g control)

@[simp] theorem controlledBitFlipMap_target (control target : Fin N) (g : Fin N → Fin 2) :
    controlledBitFlipMap control target g target = g target + g control :=
  Function.update_self target _ g

theorem controlledBitFlipMap_off (control target : Fin N) (g : Fin N → Fin 2)
    {s : Fin N} (hs : s ≠ target) :
    controlledBitFlipMap control target g s = g s :=
  Function.update_of_ne hs _ g

theorem controlledBitFlipMap_eq_self_of_control_zero (control target : Fin N)
    (g : Fin N → Fin 2) (h0 : g control = 0) :
    controlledBitFlipMap control target g = g := by
  funext s
  by_cases hs : s = target
  · rw [hs, controlledBitFlipMap_target, h0, add_zero]
  · exact controlledBitFlipMap_off control target g hs

theorem controlledBitFlipMap_target_of_control_one (control target : Fin N)
    (g : Fin N → Fin 2) (h1 : g control = 1) :
    controlledBitFlipMap control target g target = Equiv.swap (0 : Fin 2) 1 (g target) := by
  rw [controlledBitFlipMap_target, h1]
  generalize g target = x
  fin_cases x <;> decide

/-- Applying the controlled-flip map twice restores the original
configuration, provided `control ≠ target`. -/
theorem controlledBitFlipMap_involutive (control target : Fin N) (hne : control ≠ target) :
    Function.Involutive (controlledBitFlipMap control target) := by
  intro g
  funext s
  by_cases hs : s = target
  · rw [hs, controlledBitFlipMap_target, controlledBitFlipMap_target,
      controlledBitFlipMap_off control target g hne]
    have hx : ∀ x : Fin 2, x + x = 0 := by decide
    rw [add_assoc, hx, add_zero]
  · rw [controlledBitFlipMap_off control target (controlledBitFlipMap control target g) hs,
      controlledBitFlipMap_off control target g hs]

/-- The induced permutation of computational-basis configurations. -/
def controlledBitFlipEquiv (control target : Fin N) (hne : control ≠ target) :
    (Fin N → Fin 2) ≃ (Fin N → Fin 2) :=
  (controlledBitFlipMap_involutive control target hne).toPerm

@[simp] theorem controlledBitFlipEquiv_apply (control target : Fin N) (hne : control ≠ target)
    (g : Fin N → Fin 2) :
    controlledBitFlipEquiv control target hne g = controlledBitFlipMap control target g := rfl

theorem controlledBitFlipEquiv_symm_eq_self (control target : Fin N) (hne : control ≠ target) :
    (controlledBitFlipEquiv control target hne).symm = controlledBitFlipEquiv control target hne :=
  rfl

/-- The induced linear isometric equivalence on the site representation. -/
def controlledBitFlipUnitary (control target : Fin N) (hne : control ≠ target) :
    Sites N 2 ≃ₗᵢ[ℂ] Sites N 2 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (controlledBitFlipEquiv control target hne)

theorem controlledBitFlipUnitary_single (control target : Fin N)
    (hne : control ≠ target) (g : Fin N → Fin 2) :
    controlledBitFlipUnitary control target hne (EuclideanSpace.single g (1 : ℂ)) =
      EuclideanSpace.single (controlledBitFlipMap control target g) 1 := by
  rw [controlledBitFlipUnitary]
  exact EuclideanSpace.piLpCongrLeft_single _ _ _

theorem controlledBitFlipUnitary_symm_eq_self (control target : Fin N) (hne : control ≠ target) :
    (controlledBitFlipUnitary control target hne).symm = controlledBitFlipUnitary control target hne := by
  unfold controlledBitFlipUnitary
  rw [LinearIsometryEquiv.piLpCongrLeft_symm, controlledBitFlipEquiv_symm_eq_self]

/-- The two-site controlled bit-flip: the `target` bit is XORed by the
`control` bit, every other site (including `control`) unchanged. -/
theorem controlledBitFlipUnitary_local (control target : Fin N) (hne : control ≠ target) :
    IsLocalTo (controlledBitFlipUnitary control target hne).toLinearIsometry.toLinearMap
      ({control, target} : Finset (Fin N)) := by
  let cc : {x // x ∈ ({control, target} : Finset (Fin N))} := ⟨control, by simp⟩
  let tt : {x // x ∈ ({control, target} : Finset (Fin N))} := ⟨target, by simp⟩
  refine ⟨fun gl kl => if gl cc = kl cc ∧ gl tt = kl tt + kl cc then 1 else 0, ?_⟩
  intro g k
  change ⟪(EuclideanSpace.single g (1 : ℂ) : Sites N 2),
    controlledBitFlipUnitary control target hne (EuclideanSpace.single k 1)⟫_ℂ = _
  rw [controlledBitFlipUnitary_single]
  by_cases hgk : g = controlledBitFlipMap control target k
  · subst hgk
    have hoff : AgreesOff ({control, target} : Finset (Fin N))
        (controlledBitFlipMap control target k) k := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
      exact controlledBitFlipMap_off control target k hs.2
    have hcc : controlledBitFlipMap control target k control = k control :=
      controlledBitFlipMap_off control target k hne
    simp [hoff, cc, tt, hcc]
  · have hinner :
        ⟪(EuclideanSpace.single g (1 : ℂ) : Sites N 2),
          (EuclideanSpace.single (controlledBitFlipMap control target k) 1 : Sites N 2)⟫_ℂ = 0 := by
      rw [EuclideanSpace.inner_single_left]
      simp [hgk]
    rw [hinner]
    by_cases hoff : AgreesOff ({control, target} : Finset (Fin N)) g k
    · have hne2 : ¬ (g control = k control ∧ g target = k target + k control) := by
        rintro ⟨h1, h2⟩
        apply hgk
        funext s
        rcases eq_or_ne s control with hsc | hsc
        · rw [hsc, h1, (controlledBitFlipMap_off control target k hne).symm]
        rcases eq_or_ne s target with hst | hst
        · rw [hst, h2, ← controlledBitFlipMap_target control target k]
        · have hsn : s ∉ ({control, target} : Finset (Fin N)) := by simp [hsc, hst]
          rw [hoff s hsn, controlledBitFlipMap_off control target k hst]
      simp [hoff, cc, tt, hne2]
    · simp [hoff]

/-- The controlled bit-flip gate on `N` qubit sites: `target` bit XOR
`control` bit, every other site unchanged. -/
def controlledBitFlipGate (control target : Fin N) (hne : control ≠ target) :
    TwoLocalGate N 2 where
  unitary := controlledBitFlipUnitary control target hne
  support := {control, target}
  locality := controlledBitFlipUnitary_local control target hne
  support_card_le_two := (Finset.card_pair hne).le

@[simp] theorem controlledBitFlipGate_support (control target : Fin N) (hne : control ≠ target) :
    (controlledBitFlipGate control target hne).support = {control, target} := rfl

theorem controlledBitFlipGate_support_card_le_two (control target : Fin N)
    (hne : control ≠ target) :
    (controlledBitFlipGate control target hne).support.card ≤ 2 :=
  (controlledBitFlipGate control target hne).support_card_le_two

theorem controlledBitFlipGate_local (control target : Fin N) (hne : control ≠ target) :
    IsLocalTo (controlledBitFlipGate control target hne).unitary.toLinearIsometry.toLinearMap
      {control, target} :=
  (controlledBitFlipGate control target hne).locality

/-- The gate's underlying isometry is an involution: applying it twice is
the identity. -/
theorem controlledBitFlipGate_involutive (control target : Fin N) (hne : control ≠ target) :
    (controlledBitFlipGate control target hne).unitary.symm =
      (controlledBitFlipGate control target hne).unitary :=
  controlledBitFlipUnitary_symm_eq_self control target hne

/-- The gate is its own canonical inverse. -/
theorem controlledBitFlipGate_inverse (control target : Fin N) (hne : control ≠ target) :
    (controlledBitFlipGate control target hne).inverse =
      controlledBitFlipGate control target hne := by
  unfold TwoLocalGate.inverse
  congr 1
  exact controlledBitFlipGate_involutive control target hne

/-- Central semantic theorem: the controlled bit-flip gate transports the
basis vector at an arbitrary configuration `f` to the basis vector at the
XORed configuration.  This gives every information needed to compute the
action of a fanout circuit by folding this identity over a list of target
sites (as done in `IdealFanout.lean`/`NoisyGeneration.lean`). -/
theorem controlledBitFlipGate_maps_configurationBranch (control target : Fin N)
    (hne : control ≠ target) (f : Fin N → Fin 2) :
    Circuit.evalOnH [controlledBitFlipGate control target hne] (sitesEquivR N)
        (configurationBranch N f) =
      configurationBranch N (controlledBitFlipMap control target f) := by
  show Circuit.evalOnH [controlledBitFlipGate control target hne] (sitesEquivR N)
      ((sitesEquivR N).symm (EuclideanSpace.single f (1 : ℂ))) =
    (sitesEquivR N).symm (EuclideanSpace.single (controlledBitFlipMap control target f) 1)
  apply (sitesEquivR N).injective
  simp [Circuit.evalOnH]
  exact controlledBitFlipUnitary_single control target hne f

/-- Specialization: when the control bit is `0`, the configuration is
unchanged. -/
theorem controlledBitFlipGate_maps_configurationBranch_of_control_zero
    (control target : Fin N) (hne : control ≠ target) (f : Fin N → Fin 2)
    (h0 : f control = 0) :
    Circuit.evalOnH [controlledBitFlipGate control target hne] (sitesEquivR N)
        (configurationBranch N f) =
      configurationBranch N f := by
  rw [controlledBitFlipGate_maps_configurationBranch,
    controlledBitFlipMap_eq_self_of_control_zero control target f h0]

/-- Specialization: when the control bit is `1`, the target bit is
flipped. -/
theorem controlledBitFlipGate_target_of_control_one
    (control target : Fin N) (f : Fin N → Fin 2)
    (h1 : f control = 1) :
    controlledBitFlipMap control target f target = Equiv.swap (0 : Fin 2) 1 (f target) :=
  controlledBitFlipMap_target_of_control_one control target f h1

#print axioms controlledBitFlipGate_maps_configurationBranch

end

end QuantumFoundations.Complexity.Gates
