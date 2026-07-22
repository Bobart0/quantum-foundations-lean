import QuantumFoundations.Complexity.Models.Repetition.Distinguishability

/-!
# C9e — An explicit finite interference circuit

At site `r`, `bitFlipGate R r` permutes configurations by swapping the two
local bit values and leaves every other coordinate fixed.  The circuit lists
the sites in `Fin` order and therefore has exactly `R` gates.  It exchanges
the all-zero and all-one branches, proving that the model's interference
complexity is finite.
-/

namespace QuantumFoundations.Complexity.RepetitionModel

open scoped InnerProductSpace

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

/-- Flip one bit in a site configuration. -/
def bitFlipConfigurationEquiv (R : ℕ) (r : Fin R) :
    (Fin R → Fin 2) ≃ (Fin R → Fin 2) :=
  Equiv.piCongrRight fun s =>
    if s = r then Equiv.swap (0 : Fin 2) 1 else Equiv.refl _

@[simp] theorem bitFlipConfigurationEquiv_at (R : ℕ) (r : Fin R)
    (g : Fin R → Fin 2) :
    bitFlipConfigurationEquiv R r g r = Equiv.swap (0 : Fin 2) 1 (g r) := by
  simp [bitFlipConfigurationEquiv]

@[simp] theorem bitFlipConfigurationEquiv_off (R : ℕ) (r s : Fin R)
    (g : Fin R → Fin 2) (h : s ≠ r) :
    bitFlipConfigurationEquiv R r g s = g s := by
  simp [bitFlipConfigurationEquiv, h]

/-- The unitary permutation induced by flipping one configuration bit. -/
def bitFlipUnitary (R : ℕ) (r : Fin R) : Sites R 2 ≃ₗᵢ[ℂ] Sites R 2 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (bitFlipConfigurationEquiv R r)

@[simp] theorem bitFlipUnitary_configurationBasis (R : ℕ) (r : Fin R)
    (g : Fin R → Fin 2) :
    bitFlipUnitary R r (configurationBasis g) =
      configurationBasis (bitFlipConfigurationEquiv R r g) := by
  exact EuclideanSpace.piLpCongrLeft_single _ _ _

private theorem bitFlipUnitary_local (R : ℕ) (r : Fin R) :
    IsLocalTo (bitFlipUnitary R r).toLinearIsometry.toLinearMap {r} := by
  let rr : {x // x ∈ ({r} : Finset (Fin R))} := ⟨r, by simp⟩
  refine ⟨fun gl kl =>
    if gl rr = Equiv.swap (0 : Fin 2) 1 (kl rr) then 1 else 0, ?_⟩
  intro g k
  change ⟪configurationBasis g,
    bitFlipUnitary R r (configurationBasis k)⟫_ℂ = _
  rw [bitFlipUnitary_configurationBasis]
  by_cases hgf : g = bitFlipConfigurationEquiv R r k
  · subst g
    have hoff : AgreesOff {r} (bitFlipConfigurationEquiv R r k) k := by
      intro s hs
      exact bitFlipConfigurationEquiv_off R r s k (by simpa using hs)
    simp [configurationBasis, hoff, rr]
  · have hinner :
        ⟪configurationBasis g,
          configurationBasis (bitFlipConfigurationEquiv R r k)⟫_ℂ = 0 := by
      unfold configurationBasis
      rw [EuclideanSpace.inner_single_left]
      simp [hgf]
    by_cases hoff : AgreesOff {r} g k
    · have hsite :
          g r ≠ bitFlipConfigurationEquiv R r k r := by
        intro hr
        apply hgf
        funext s
        by_cases hsr : s = r
        · simpa [hsr] using hr
        · rw [bitFlipConfigurationEquiv_off R r s k hsr]
          exact hoff s (by simpa using hsr)
      have hsite' : g r ≠ Equiv.swap (0 : Fin 2) 1 (k r) := by
        simpa using hsite
      rw [hinner]
      simp [hoff, rr, hsite']
    · rw [hinner]
      simp [hoff]

/-- One exact one-site Pauli-X gate. -/
def bitFlipGate (R : ℕ) (r : Fin R) : TwoLocalGate R 2 where
  unitary := bitFlipUnitary R r
  support := {r}
  locality := bitFlipUnitary_local R r
  support_card_le_two := by simp

@[simp] theorem bitFlipGate_support (R : ℕ) (r : Fin R) :
    (bitFlipGate R r).support = {r} := rfl

theorem bitFlipGate_local (R : ℕ) (r : Fin R) :
    IsLocalTo (bitFlipGate R r).unitary.toLinearIsometry.toLinearMap {r} :=
  (bitFlipGate R r).locality

/-- Apply the chronological circuit of flips indexed by a list of sites. -/
private theorem eval_bitFlip_list_configuration (R : ℕ)
    (rs : List (Fin R)) (g : Fin R → Fin 2) :
    Circuit.eval (rs.map (bitFlipGate R)) (configurationBasis g) =
      configurationBasis
        (rs.foldl (fun h r => bitFlipConfigurationEquiv R r h) g) := by
  induction rs generalizing g with
  | nil => rfl
  | cons r rs ih =>
      change Circuit.eval (rs.map (bitFlipGate R))
          (bitFlipUnitary R r (configurationBasis g)) = _
      rw [bitFlipUnitary_configurationBasis, ih]
      rfl

private theorem foldl_bitFlips_apply_of_nodup (R : ℕ)
    {rs : List (Fin R)} (hrs : rs.Nodup) (g : Fin R → Fin 2) (s : Fin R) :
    (rs.foldl (fun h r => bitFlipConfigurationEquiv R r h) g) s =
      if s ∈ rs then Equiv.swap (0 : Fin 2) 1 (g s) else g s := by
  induction rs generalizing g with
  | nil => simp
  | cons r rs ih =>
      have hr : r ∉ rs := (List.nodup_cons.mp hrs).1
      have hrs' : rs.Nodup := (List.nodup_cons.mp hrs).2
      rw [List.foldl_cons, ih hrs']
      by_cases hsr : s = r
      · subst s
        simp [hr]
      · by_cases hs : s ∈ rs
        · simp [hs, hsr, bitFlipConfigurationEquiv_off]
        · simp [hs, hsr, bitFlipConfigurationEquiv_off]

private theorem foldl_all_bitFlips_zero (R : ℕ) :
    (List.finRange R).foldl
        (fun h r => bitFlipConfigurationEquiv R r h) (zeroConfiguration R) =
      oneConfiguration R := by
  funext s
  rw [foldl_bitFlips_apply_of_nodup R (List.nodup_finRange R)]
  simp [zeroConfiguration, oneConfiguration]

private theorem foldl_all_bitFlips_one (R : ℕ) :
    (List.finRange R).foldl
        (fun h r => bitFlipConfigurationEquiv R r h) (oneConfiguration R) =
      zeroConfiguration R := by
  funext s
  rw [foldl_bitFlips_apply_of_nodup R (List.nodup_finRange R)]
  simp [zeroConfiguration, oneConfiguration]

/-- Flip every site once, in increasing `Fin` order. -/
def allBitFlipCircuit (R : ℕ) : Circuit R 2 :=
  (List.finRange R).map (bitFlipGate R)

@[simp] theorem allBitFlipCircuit_length (R : ℕ) :
    (allBitFlipCircuit R).length = R := by
  simp [allBitFlipCircuit, Circuit.length]

/-- The explicit `R`-gate circuit maps the all-zero branch to all one. -/
theorem allBitFlipCircuit_maps_zero_to_one (R : ℕ) :
    Circuit.evalOnH (allBitFlipCircuit R) (sitesEquivR R) (zeroBranch R) =
      oneBranch R := by
  apply (sitesEquivR R).injective
  simp [Circuit.evalOnH]
  rw [show sitesZero R = configurationBasis (zeroConfiguration R) from rfl]
  rw [show sitesOne R = configurationBasis (oneConfiguration R) from rfl]
  rw [allBitFlipCircuit, eval_bitFlip_list_configuration,
    foldl_all_bitFlips_zero]

/-- The same circuit maps the all-one branch to all zero. -/
theorem allBitFlipCircuit_maps_one_to_zero (R : ℕ) :
    Circuit.evalOnH (allBitFlipCircuit R) (sitesEquivR R) (oneBranch R) =
      zeroBranch R := by
  apply (sitesEquivR R).injective
  simp [Circuit.evalOnH]
  rw [show sitesOne R = configurationBasis (oneConfiguration R) from rfl]
  rw [show sitesZero R = configurationBasis (zeroConfiguration R) from rfl]
  rw [allBitFlipCircuit, eval_bitFlip_list_configuration,
    foldl_all_bitFlips_one]

/-- The all-bit-flip circuit interferes the two branches at threshold one. -/
theorem repetition_interferesAt_one (R : ℕ) :
    InterferesAt (sitesEquivR R) (zeroBranch R) (oneBranch R) 1
      (allBitFlipCircuit R) := by
  unfold InterferesAt
  rw [allBitFlipCircuit_maps_one_to_zero, allBitFlipCircuit_maps_zero_to_one,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    zeroBranch_norm, oneBranch_norm]
  norm_num

/-- The explicit witness proves the interference complexity is at most `R`. -/
theorem repetition_interferenceComplexity_upper (R : ℕ) :
    interferenceComplexity
      (sitesEquivR R) (zeroBranch R) (oneBranch R) 1 ≤ (R : WithTop ℕ) := by
  unfold interferenceComplexity
  calc
    minCircuitLength (InterferesAt (sitesEquivR R) (zeroBranch R) (oneBranch R) 1)
        ≤ ((allBitFlipCircuit R).length : WithTop ℕ) :=
      minCircuitLength_le_of_witness
        (allBitFlipCircuit R) (repetition_interferesAt_one R)
    _ = R := by rw [allBitFlipCircuit_length]

#print axioms allBitFlipCircuit_maps_zero_to_one
#print axioms repetition_interferenceComplexity_upper

end


end QuantumFoundations.Complexity.RepetitionModel
