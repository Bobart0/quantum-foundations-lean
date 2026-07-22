import QuantumFoundations.Complexity.Models.NoisyRepetition.Complexities
import QuantumFoundations.Complexity.Models.Repetition.Interference

/-!
# C10f — Finite noisy interference witness

Flipping every one of the `R + 1` sites (source and records alike) swaps the
source bit as well as every record bit, so it exchanges the two same-source
configurations pairwise: `config00 ↔ config11` and `config01 ↔ config10`.
Consequently the all-bit-flip circuit exchanges the two noisy branches
exactly, giving a finite interference witness of length `R + 1`.  No
robustness hypothesis is needed for this upper bound: it is an exact circuit
identity.
-/

namespace QuantumFoundations.Complexity.NoisyRepetitionModel

open scoped InnerProductSpace

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.RepetitionModel

noncomputable section

/-! ## C10f.1 — Action of the all-bit-flip circuit on the four configurations -/

theorem allBitFlip_flip_config00 (R : ℕ) :
    (fun s => Equiv.swap (0 : Fin 2) 1 (config00 R s)) = config11 R := by
  funext s
  simp [config00, config11]

theorem allBitFlip_flip_config11 (R : ℕ) :
    (fun s => Equiv.swap (0 : Fin 2) 1 (config11 R s)) = config00 R := by
  funext s
  simp [config00, config11]

theorem allBitFlip_flip_config01 (R : ℕ) :
    (fun s => Equiv.swap (0 : Fin 2) 1 (config01 R s)) = config10 R := by
  funext s
  refine Fin.cases ?_ ?_ s
  · simp [config01, config10]
  · intro r
    simp [config01, config10]

theorem allBitFlip_flip_config10 (R : ℕ) :
    (fun s => Equiv.swap (0 : Fin 2) 1 (config10 R s)) = config01 R := by
  funext s
  refine Fin.cases ?_ ?_ s
  · simp [config01, config10]
  · intro r
    simp [config01, config10]

/-! ## C10f.2 — Action on the four basis states -/

theorem allBitFlip_maps_basis00_to_basis11 (R : ℕ) :
    Circuit.evalOnH (allBitFlipCircuit (R + 1)) (sitesEquivR (R + 1)) (basis00 R) =
      basis11 R := by
  unfold basis00 basis11
  rw [allBitFlipCircuit_maps_configurationBranch, allBitFlip_flip_config00]

theorem allBitFlip_maps_basis11_to_basis00 (R : ℕ) :
    Circuit.evalOnH (allBitFlipCircuit (R + 1)) (sitesEquivR (R + 1)) (basis11 R) =
      basis00 R := by
  unfold basis00 basis11
  rw [allBitFlipCircuit_maps_configurationBranch, allBitFlip_flip_config11]

theorem allBitFlip_maps_basis01_to_basis10 (R : ℕ) :
    Circuit.evalOnH (allBitFlipCircuit (R + 1)) (sitesEquivR (R + 1)) (basis01 R) =
      basis10 R := by
  unfold basis01 basis10
  rw [allBitFlipCircuit_maps_configurationBranch, allBitFlip_flip_config01]

theorem allBitFlip_maps_basis10_to_basis01 (R : ℕ) :
    Circuit.evalOnH (allBitFlipCircuit (R + 1)) (sitesEquivR (R + 1)) (basis10 R) =
      basis01 R := by
  unfold basis01 basis10
  rw [allBitFlipCircuit_maps_configurationBranch, allBitFlip_flip_config10]

/-! ## C10f.3 — Action on the two noisy branches -/

theorem allBitFlip_maps_noisyZero_to_noisyOne (p : NoiseProfile) (R : ℕ) :
    Circuit.evalOnH (allBitFlipCircuit (R + 1)) (sitesEquivR (R + 1))
        (noisyZeroBranch p R) =
      noisyOneBranch p R := by
  simp only [noisyZeroBranch, noisyOneBranch, map_add, map_smul,
    allBitFlip_maps_basis00_to_basis11, allBitFlip_maps_basis01_to_basis10]
  abel

theorem allBitFlip_maps_noisyOne_to_noisyZero (p : NoiseProfile) (R : ℕ) :
    Circuit.evalOnH (allBitFlipCircuit (R + 1)) (sitesEquivR (R + 1))
        (noisyOneBranch p R) =
      noisyZeroBranch p R := by
  simp only [noisyZeroBranch, noisyOneBranch, map_add, map_smul,
    allBitFlip_maps_basis10_to_basis01, allBitFlip_maps_basis11_to_basis00]
  abel

/-! ## C10f.4 — Interference witness and complexity bounds -/

/-- The all-bit-flip circuit exchanges the two noisy branches exactly, so it
interferes them at threshold `1 / 2` (indeed at threshold `1`). No
robustness hypothesis is needed. -/
theorem noisy_allBitFlip_interferesAt_half (p : NoiseProfile) (R : ℕ) [NeZero R] :
    InterferesAt (sitesEquivR (R + 1))
      (noisyZeroBranch p R) (noisyOneBranch p R) (1 / 2 : ℝ)
      (allBitFlipCircuit (R + 1)) := by
  unfold InterferesAt
  rw [allBitFlip_maps_noisyOne_to_noisyZero, allBitFlip_maps_noisyZero_to_noisyOne,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    noisyZeroBranch_norm, noisyOneBranch_norm]
  norm_num

/-- The explicit `(R + 1)`-gate witness bounds the interference complexity. -/
theorem noisy_repetition_interference_upper (p : NoiseProfile) (R : ℕ) [NeZero R] :
    interferenceComplexity (sitesEquivR (R + 1))
        (noisyZeroBranch p R) (noisyOneBranch p R) (1 / 2 : ℝ)
      ≤ ((R + 1 : ℕ) : WithTop ℕ) := by
  unfold interferenceComplexity
  calc
    minCircuitLength
        (InterferesAt (sitesEquivR (R + 1))
          (noisyZeroBranch p R) (noisyOneBranch p R) (1 / 2 : ℝ))
        ≤ ((allBitFlipCircuit (R + 1)).length : WithTop ℕ) :=
      minCircuitLength_le_of_witness
        (allBitFlipCircuit (R + 1)) (noisy_allBitFlip_interferesAt_half p R)
    _ = ((R + 1 : ℕ) : WithTop ℕ) := by rw [allBitFlipCircuit_length]

/-- Combined interference-complexity bounds: `ceilHalf R` from bottom (under
robust noise) and `R + 1` from the explicit witness (unconditionally). -/
theorem noisy_repetition_interference_bounds
    (p : NoiseProfile) (R : ℕ) [NeZero R] (hp : p.IsRobust) :
    (ceilHalf R : WithTop ℕ) ≤
        interferenceComplexity (sitesEquivR (R + 1))
          (noisyZeroBranch p R) (noisyOneBranch p R) (1 / 2 : ℝ) ∧
      interferenceComplexity (sitesEquivR (R + 1))
          (noisyZeroBranch p R) (noisyOneBranch p R) (1 / 2 : ℝ)
        ≤ ((R + 1 : ℕ) : WithTop ℕ) :=
  ⟨noisy_repetition_interference_lower p R hp, noisy_repetition_interference_upper p R⟩

/-- The noisy interference complexity is finite. -/
theorem noisy_repetition_interference_ne_top (p : NoiseProfile) (R : ℕ) [NeZero R] :
    interferenceComplexity (sitesEquivR (R + 1))
        (noisyZeroBranch p R) (noisyOneBranch p R) (1 / 2 : ℝ) ≠ ⊤ :=
  ne_top_of_le_ne_top WithTop.coe_ne_top (noisy_repetition_interference_upper p R)

end

end QuantumFoundations.Complexity.NoisyRepetitionModel
