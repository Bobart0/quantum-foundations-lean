import QuantumFoundations.Complexity.Gates.AmplitudeRotation
import QuantumFoundations.Complexity.Models.MeasurementGeneration.BranchWeights

/-!
# C11e — Profile-preparation gate for the first record qubit

`ImplementsNoisePreparation p R` is the smallest useful certificate for a
gate implementing `NoiseProfile p`'s local action `|0⟩ ↦ keep|0⟩ + leak|1⟩`
at the first record qubit (`firstRecord R := recordSite (0 : Fin R)`), while
leaving every other site (including the source) unchanged.  Note this is
*not* the same as mapping `basis00`/`basis10` all the way to
`noisyZeroBranch`/`noisyOneBranch`: it only flips the first record's own
bit, producing an intermediate state with just *one* excited record.  The
record-cat fanout of C11f is what subsequently copies that single bit to
every other record.

The canonical construction from every `NoiseProfile`, `profilePreparationGate`,
is obtained directly from the generic `amplitudeRotationGate` of C11e's
`Gates.AmplitudeRotation`: no supplied-gate hypothesis is needed anywhere in
C11.
-/

namespace QuantumFoundations.Complexity.MeasurementGeneration

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.Gates
open QuantumFoundations.Complexity.RepetitionModel
open QuantumFoundations.Complexity.NoisyRepetitionModel

noncomputable section

/-- The first record qubit, embedded at site `recordSite (0 : Fin R)`. -/
def firstRecord (R : ℕ) [NeZero R] : Fin (R + 1) := recordSite (0 : Fin R)

/-- A supplied gate implementing `p`'s local preparation action at the first
record qubit: its support is confined to `firstRecord R`, and its action on
the two blank-record basis states (`basis00`/`basis10`, both with first
record `0`) matches the local rotation. -/
structure ImplementsNoisePreparation (p : NoiseProfile) (R : ℕ) [NeZero R] where
  /-- The supplied gate. -/
  gate : TwoLocalGate (R + 1) 2
  /-- The gate touches only the first record qubit. -/
  support_subset : gate.support ⊆ {firstRecord R}
  /-- Action on the all-zero-source-`0` configuration. -/
  maps_basis00 : Circuit.evalOnH [gate] (sitesEquivR (R + 1)) (basis00 R) =
    p.keep • basis00 R
      + p.leak • configurationBranch (R + 1)
        (bitFlipConfigurationEquiv (R + 1) (firstRecord R) (config00 R))
  /-- Action on the all-zero-source-`1` configuration. -/
  maps_basis10 : Circuit.evalOnH [gate] (sitesEquivR (R + 1)) (basis10 R) =
    p.keep • basis10 R
      + p.leak • configurationBranch (R + 1)
        (bitFlipConfigurationEquiv (R + 1) (firstRecord R) (config10 R))

/-- The canonical preparation gate at the first record qubit, for every
`NoiseProfile`. -/
def profilePreparationGate (p : NoiseProfile) (R : ℕ) [NeZero R] : TwoLocalGate (R + 1) 2 :=
  amplitudeRotationGate p (firstRecord R)

@[simp] theorem profilePreparationGate_support (p : NoiseProfile) (R : ℕ) [NeZero R] :
    (profilePreparationGate p R).support = {firstRecord R} :=
  amplitudeRotationGate_support p (firstRecord R)

theorem profilePreparationGate_maps_basis00 (p : NoiseProfile) (R : ℕ) [NeZero R] :
    Circuit.evalOnH [profilePreparationGate p R] (sitesEquivR (R + 1)) (basis00 R) =
      p.keep • basis00 R
        + p.leak • configurationBranch (R + 1)
          (bitFlipConfigurationEquiv (R + 1) (firstRecord R) (config00 R)) :=
  amplitudeRotationGate_maps_configurationBranch_of_zero p (firstRecord R) (config00 R)
    (config00_record R 0)

theorem profilePreparationGate_maps_basis10 (p : NoiseProfile) (R : ℕ) [NeZero R] :
    Circuit.evalOnH [profilePreparationGate p R] (sitesEquivR (R + 1)) (basis10 R) =
      p.keep • basis10 R
        + p.leak • configurationBranch (R + 1)
          (bitFlipConfigurationEquiv (R + 1) (firstRecord R) (config10 R)) :=
  amplitudeRotationGate_maps_configurationBranch_of_zero p (firstRecord R) (config10 R)
    (config10_record R 0)

/-- The canonical preparation gate, packaged as a certificate: constructed
for every `NoiseProfile`, not merely assumed to exist. -/
def profilePreparationImplementation (p : NoiseProfile) (R : ℕ) [NeZero R] :
    ImplementsNoisePreparation p R where
  gate := profilePreparationGate p R
  support_subset := le_of_eq (profilePreparationGate_support p R)
  maps_basis00 := profilePreparationGate_maps_basis00 p R
  maps_basis10 := profilePreparationGate_maps_basis10 p R

#print axioms profilePreparationImplementation

end

end QuantumFoundations.Complexity.MeasurementGeneration
