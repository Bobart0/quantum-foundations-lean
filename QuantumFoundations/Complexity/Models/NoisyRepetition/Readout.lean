import QuantumFoundations.Complexity.Models.NoisyRepetition.Records
import QuantumFoundations.Complexity.Models.Repetition.Readout
import QuantumFoundations.Complexity.ApproxRecordDistinguishability

/-!
# C10d — Exact readout at an arbitrary noisy record site

The noisy model reads out record qubit `0` (embedded at site `recordSite
(0 : Fin R)`) with the arbitrary-site reflection gate `recordReadoutCircuitAt`
added to the C9 repetition model in `Readout.lean`.  The readout circuit
implements the *exact* abstract record phase flip; combined with the
approximate records of C10c it becomes an *approximate* implementation on the
two noisy branches at error `ξ = 0`, via the existing C8 exact-to-approximate
bridge.
-/

namespace QuantumFoundations.Complexity.NoisyRepetitionModel

open scoped InnerProductSpace

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.RepetitionModel

noncomputable section

/-- The one-gate readout for record qubit `0`, embedded at
`recordSite (0 : Fin R)` of the `R + 1`-site model. -/
def noisyReadoutCircuit (R : ℕ) [NeZero R] : Circuit (R + 1) 2 :=
  recordReadoutCircuitAt (R + 1) (recordSite (0 : Fin R))

@[simp] theorem noisyReadoutCircuit_length (R : ℕ) [NeZero R] :
    (noisyReadoutCircuit R).length = 1 :=
  recordReadoutCircuitAt_length (R + 1) (recordSite (0 : Fin R))

/-- The one-gate readout implements the exact abstract record phase flip on
the exact record at record qubit `0`. -/
theorem noisyReadoutCircuit_implements (R : ℕ) [NeZero R] :
    ImplementsRecordPhaseFlip
      (sitesEquivR (R + 1)) (noisyReadoutCircuit R) (noisyRecords R 0) 1 :=
  recordReadoutCircuitAt_implements (R + 1) (recordSite (0 : Fin R))

/-- The exact readout is therefore also an approximate implementation of the
record phase flip on the two noisy branches, at pointwise error `0`. -/
theorem noisyReadoutCircuit_approximatesRecordPhaseFlipOn
    (p : NoiseProfile) (R : ℕ) [NeZero R] :
    ApproximatesRecordPhaseFlipOn
      (sitesEquivR (R + 1)) (noisyReadoutCircuit R) (noisyRecords R 0) 1
      (noisyZeroBranch p R) (noisyOneBranch p R) 0 :=
  implementsRecordPhaseFlip_gives_approximation_zero
    (sitesEquivR (R + 1)) (noisyReadoutCircuit R) (noisyRecords R 0) 1
    (noisyZeroBranch p R) (noisyOneBranch p R) (noisyReadoutCircuit_implements R)

#print axioms noisyReadoutCircuit_implements

end

end QuantumFoundations.Complexity.NoisyRepetitionModel
