import QuantumFoundations.Complexity.Gates.ControlledBitFlip
import QuantumFoundations.Complexity.Models.NoisyRepetition.States

/-!
# C11b — Ideal unitary measurement fanout

The source qubit controls a bit flip on every record qubit: for each
`r : Fin R`, `sourceRecordGate R r` XORs record `r`'s bit by the source
bit, leaving every other site (including the source) unchanged.  Listing
one such gate per record site gives `idealFanoutCircuit R`, a length-`R`
circuit.

This is exactly computational-basis label fanout: the circuit copies the
*classical* value of the source bit into every blank record, the same
`CNOT`-fanout used to prepare a GHZ-type state from `α|0⟩ + β|1⟩`.  It does
**not** clone an arbitrary quantum state — an unknown superposition cannot be
copied by any unitary (no-cloning); here only the *computational-basis
label* is fanned out, exactly as the `R`-fold XOR/CNOT circuits used for
classical error-correction encoding.
-/

namespace QuantumFoundations.Complexity.MeasurementGeneration

open scoped InnerProductSpace Classical

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.Gates
open QuantumFoundations.Complexity.RepetitionModel
open QuantumFoundations.Complexity.NoisyRepetitionModel

noncomputable section

/-! ## C11b.1 — The fanout circuit -/

/-- The source-controlled bit flip on record site `r`. -/
def sourceRecordGate (R : ℕ) (r : Fin R) : TwoLocalGate (R + 1) 2 :=
  controlledBitFlipGate (sourceSite R) (recordSite r) (recordSite_ne_sourceSite r).symm

/-- One source-controlled flip per record site, in increasing `Fin` order. -/
def idealFanoutCircuit (R : ℕ) : Circuit (R + 1) 2 :=
  (List.finRange R).map (sourceRecordGate R)

@[simp] theorem idealFanoutCircuit_length (R : ℕ) :
    (idealFanoutCircuit R).length = R := by
  simp [idealFanoutCircuit, Circuit.length]

/-- The circuit's union support has at most `2 * R` sites, from the generic
`2`-local bound: each of the `R` gates touches at most two sites (the source
and one record). -/
theorem idealFanoutCircuit_support_card_le (R : ℕ) :
    (idealFanoutCircuit R).support.card ≤ 2 * R := by
  have h := Circuit.circuit_support_card_le (idealFanoutCircuit R)
  rwa [idealFanoutCircuit_length] at h

/-! ## C11b.2 — Action on computational-basis configurations -/

/-- Folding the controlled-flip map with a fixed control never changes the
control site itself. -/
private theorem foldl_sourceRecord_source_eq (R : ℕ) (rs : List (Fin R))
    (f : Fin (R + 1) → Fin 2) :
    (rs.foldl (fun h r => controlledBitFlipMap (sourceSite R) (recordSite r) h) f)
        (sourceSite R) = f (sourceSite R) := by
  induction rs generalizing f with
  | nil => rfl
  | cons r rs ih =>
      rw [List.foldl_cons, ih]
      exact controlledBitFlipMap_off (sourceSite R) (recordSite r) f
        (recordSite_ne_sourceSite r).symm

/-- Over a `Nodup` list, folding the controlled-flip map touches each listed
record site exactly once: its final bit gains the (unchanging) source bit
exactly when its index is listed. -/
private theorem foldl_sourceRecord_record_apply_of_nodup (R : ℕ) {rs : List (Fin R)}
    (hrs : rs.Nodup) (f : Fin (R + 1) → Fin 2) (r : Fin R) :
    (rs.foldl (fun h r' => controlledBitFlipMap (sourceSite R) (recordSite r') h) f)
        (recordSite r) =
      if r ∈ rs then f (recordSite r) + f (sourceSite R) else f (recordSite r) := by
  induction rs generalizing f with
  | nil => simp
  | cons r' rs ih =>
      have hr'nin : r' ∉ rs := (List.nodup_cons.mp hrs).1
      have hrs' : rs.Nodup := (List.nodup_cons.mp hrs).2
      rw [List.foldl_cons, ih hrs']
      by_cases hrr : r = r'
      · subst hrr
        have hstep : controlledBitFlipMap (sourceSite R) (recordSite r) f (recordSite r)
            = f (recordSite r) + f (sourceSite R) := controlledBitFlipMap_target _ _ _
        have hsrc : controlledBitFlipMap (sourceSite R) (recordSite r) f (sourceSite R)
            = f (sourceSite R) :=
          controlledBitFlipMap_off _ _ f (recordSite_ne_sourceSite r).symm
        rw [hstep, hsrc]
        simp [hr'nin]
      · have hne' : recordSite r ≠ recordSite r' := fun heq => hrr (recordSite_injective heq)
        rw [controlledBitFlipMap_off (sourceSite R) (recordSite r') f hne',
          controlledBitFlipMap_off (sourceSite R) (recordSite r') f
            (recordSite_ne_sourceSite r').symm]
        by_cases hmem : r ∈ rs
        · simp [hmem, hrr]
        · simp [hmem, hrr]

/-- The action of the fanout circuit on the site representation of an
arbitrary configuration. -/
private theorem eval_sourceRecord_list_configuration (R : ℕ) (rs : List (Fin R))
    (f : Fin (R + 1) → Fin 2) :
    Circuit.eval (rs.map (sourceRecordGate R)) (EuclideanSpace.single f (1 : ℂ)) =
      EuclideanSpace.single
        (rs.foldl (fun h r => controlledBitFlipMap (sourceSite R) (recordSite r) h) f) 1 := by
  induction rs generalizing f with
  | nil => rfl
  | cons r rs ih =>
      change Circuit.eval (rs.map (sourceRecordGate R))
          (controlledBitFlipUnitary (sourceSite R) (recordSite r) (recordSite_ne_sourceSite r).symm
            (EuclideanSpace.single f 1)) = _
      rw [controlledBitFlipUnitary_single, ih]
      rfl

/-- Every site of `Fin (R + 1)` is either the source or a unique record.
Not `private`: also reused directly by `NoisyGeneration.lean`. -/
theorem eq_sourceSite_or_recordSite (R : ℕ) (s : Fin (R + 1)) :
    s = sourceSite R ∨ ∃ r : Fin R, s = recordSite r :=
  Fin.cases (Or.inl rfl) (fun r => Or.inr ⟨r, rfl⟩) s

/-- The fanout circuit's full action on an arbitrary configuration: the
source bit is unchanged, and every record bit gains the (fixed) source
bit. -/
theorem idealFanout_maps_configurationBranch (R : ℕ) (f : Fin (R + 1) → Fin 2) :
    Circuit.evalOnH (idealFanoutCircuit R) (sitesEquivR (R + 1)) (configurationBranch (R + 1) f) =
      configurationBranch (R + 1)
        (fun s => if s = sourceSite R then f (sourceSite R) else f s + f (sourceSite R)) := by
  show Circuit.evalOnH (idealFanoutCircuit R) (sitesEquivR (R + 1))
      ((sitesEquivR (R + 1)).symm (EuclideanSpace.single f (1 : ℂ))) =
    (sitesEquivR (R + 1)).symm (EuclideanSpace.single
      (fun s => if s = sourceSite R then f (sourceSite R) else f s + f (sourceSite R)) 1)
  apply (sitesEquivR (R + 1)).injective
  simp [Circuit.evalOnH]
  rw [idealFanoutCircuit, eval_sourceRecord_list_configuration]
  congr 1
  funext s
  rcases eq_sourceSite_or_recordSite R s with hs | ⟨r, hs⟩
  · subst hs
    rw [foldl_sourceRecord_source_eq]
    simp
  · subst hs
    rw [foldl_sourceRecord_record_apply_of_nodup R (List.nodup_finRange R)]
    simp [recordSite_ne_sourceSite]

theorem idealFanout_maps_basis00 (R : ℕ) :
    Circuit.evalOnH (idealFanoutCircuit R) (sitesEquivR (R + 1)) (basis00 R) = basis00 R := by
  unfold basis00
  rw [idealFanout_maps_configurationBranch]
  congr 1
  funext s
  by_cases hs : s = sourceSite R <;> simp [hs, config00]

theorem idealFanout_maps_basis01 (R : ℕ) :
    Circuit.evalOnH (idealFanoutCircuit R) (sitesEquivR (R + 1)) (basis01 R) = basis01 R := by
  unfold basis01
  rw [idealFanout_maps_configurationBranch]
  congr 1
  funext s
  by_cases hs : s = sourceSite R
  · simp [hs]
  · obtain ⟨r, rfl⟩ := (eq_sourceSite_or_recordSite R s).resolve_left hs
    simp [hs, config01_record, config01_source]

theorem idealFanout_maps_basis10 (R : ℕ) :
    Circuit.evalOnH (idealFanoutCircuit R) (sitesEquivR (R + 1)) (basis10 R) = basis11 R := by
  unfold basis10 basis11
  rw [idealFanout_maps_configurationBranch]
  congr 1
  funext s
  by_cases hs : s = sourceSite R
  · simp [hs]
  · obtain ⟨r, rfl⟩ := (eq_sourceSite_or_recordSite R s).resolve_left hs
    simp [hs, config10_record, config10_source]

theorem idealFanout_maps_basis11 (R : ℕ) :
    Circuit.evalOnH (idealFanoutCircuit R) (sitesEquivR (R + 1)) (basis11 R) = basis10 R := by
  unfold basis10 basis11
  rw [idealFanout_maps_configurationBranch]
  congr 1
  funext s
  by_cases hs : s = sourceSite R
  · simp [hs]
  · obtain ⟨r, rfl⟩ := (eq_sourceSite_or_recordSite R s).resolve_left hs
    have hx : ∀ x : Fin 2, x + 1 = if x = 1 then 0 else 1 := by decide
    simp [hs, config11_record, config11_source]

/-! ## C11b.3 — Generic branching from a source superposition -/

/-- Pre-measurement state: source superposition, all records blank
(all-zero). -/
def idealInputState (α β : ℂ) (R : ℕ) : H (2 ^ (R + 1)) :=
  α • basis00 R + β • basis10 R

/-- Post-measurement state: each source branch carries its own constant
record tail. -/
def idealOutputState (α β : ℂ) (R : ℕ) : H (2 ^ (R + 1)) :=
  α • basis00 R + β • basis11 R

/-- The ideal fanout circuit turns a source superposition over blank
records into the branching decomposition, by linearity from the two basis
actions.  This is computational-basis fanout, not cloning of an arbitrary
superposition: the source qubit's own amplitudes `α, β` are never copied,
only its classical `0`/`1` label is correlated with the (initially blank)
records. -/
theorem idealFanout_generates_branching (α β : ℂ) (R : ℕ) :
    Circuit.evalOnH (idealFanoutCircuit R) (sitesEquivR (R + 1)) (idealInputState α β R) =
      idealOutputState α β R := by
  unfold idealInputState idealOutputState
  rw [map_add, map_smul, map_smul, idealFanout_maps_basis00, idealFanout_maps_basis10]

#print axioms idealFanout_generates_branching

end

end QuantumFoundations.Complexity.MeasurementGeneration
