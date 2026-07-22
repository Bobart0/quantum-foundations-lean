import QuantumFoundations.Complexity.Models.MeasurementGeneration.ProfilePreparation

/-!
# C11f/C11g — Noisy redundant-record generation

The noisy branches are unitarily generated in two stages, each a finite
`2`-local circuit:

1. `recordCatPreparationCircuit p R`: the profile-preparation gate at the
   first record (C11e), *followed by* a "cat" fanout that copies the first
   record's own bit to every other record, controlled by the first record
   itself.  Applied to `basis00`/`basis10` (both blank, i.e. first record
   `0`), this produces `keep • basis00 + leak • basis01` /
   `keep • basis10 + leak • basis11`.
2. `idealFanoutCircuit R` (C11b): the source-controlled fanout onto *every*
   record, including the first.  Applied to the two states above, this
   leaves the (source-`0`) first exactly unchanged, and exchanges the two
   (source-`1`) terms of the second, producing exactly `noisyZeroBranch`
   and `noisyOneBranch`.

`noisyMeasurementCircuit p R := recordCatPreparationCircuit p R ++
idealFanoutCircuit R` is the full generation circuit (`eval (C ++ D) = eval D
∘ eval C`: `C` first, `D` second, per `Circuit.eval_append`).
-/

namespace QuantumFoundations.Complexity.MeasurementGeneration

open scoped Classical

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.Gates
open QuantumFoundations.Complexity.RepetitionModel
open QuantumFoundations.Complexity.NoisyRepetitionModel

noncomputable section

/-! ## C11f.1 — The non-first record sites -/

/-- Every record index other than `0`. -/
def nonFirstRecords (R : ℕ) [NeZero R] : List (Fin R) :=
  (List.finRange R).filter (· ≠ (0 : Fin R))

theorem nonFirstRecords_nodup (R : ℕ) [NeZero R] : (nonFirstRecords R).Nodup :=
  (List.nodup_finRange R).filter _

theorem mem_nonFirstRecords (R : ℕ) [NeZero R] (r : Fin R) :
    r ∈ nonFirstRecords R ↔ r ≠ 0 := by
  unfold nonFirstRecords
  simp [List.mem_filter, List.mem_finRange]

theorem zero_notMem_nonFirstRecords (R : ℕ) [NeZero R] : (0 : Fin R) ∉ nonFirstRecords R := by
  simp [mem_nonFirstRecords]

/-- The generic fact that filtering a list splits its length additively. -/
private theorem filter_partition_length {α : Type*} (l : List α) (p : α → Prop)
    [DecidablePred p] :
    (l.filter p).length + (l.filter (fun x => ¬ p x)).length = l.length := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : p a <;> simp [h, ← ih] <;> omega

theorem nonFirstRecords_length (R : ℕ) [NeZero R] : (nonFirstRecords R).length = R - 1 := by
  have hpart := filter_partition_length (List.finRange R) (fun x : Fin R => x ≠ 0)
  rw [List.length_finRange] at hpart
  have hone : ((List.finRange R).filter (fun x : Fin R => ¬ x ≠ 0)).length = 1 := by
    rw [List.filter_congr (l := List.finRange R)
      (p := fun x : Fin R => decide (¬ x ≠ 0)) (q := fun x : Fin R => decide (x = 0))
      (fun x _ => by simp)]
    rw [List.filter_eq]
    simp
  unfold nonFirstRecords
  omega

/-! ## C11f.2 — Generic controlled-flip fold over an exclusion list -/

/-- Folding the controlled-flip map (through an embedding `emb` of the
target-list index type into the control's site type) leaves any site `s`
that is never an embedded target unchanged.  Applied with `s := control`
this shows the control site is unaffected; applied with any other untouched
site (e.g. the source site) it shows that site is unaffected too. -/
private theorem foldl_controlledFlip_untouched_eq {M R : ℕ} (control : Fin M) (emb : Fin R → Fin M)
    (targets : List (Fin R)) (s : Fin M) (hs : ∀ r ∈ targets, s ≠ emb r) (f : Fin M → Fin 2) :
    (targets.foldl (fun h r => controlledBitFlipMap control (emb r) h) f) s = f s := by
  induction targets generalizing f with
  | nil => rfl
  | cons r rs ih =>
      have hr : s ≠ emb r := hs r List.mem_cons_self
      have hrs : ∀ r' ∈ rs, s ≠ emb r' := fun r' hr' => hs r' (List.mem_cons_of_mem r hr')
      rw [List.foldl_cons, ih hrs]
      exact controlledBitFlipMap_off control (emb r) f hr

/-- Over a `Nodup` exclusion-list, folding touches each embedded target
exactly once: its final bit gains the (unchanging) control bit exactly when
listed. -/
private theorem foldl_controlledFlip_target_apply {M R : ℕ} (control : Fin M)
    (emb : Fin R → Fin M) (hemb : Function.Injective emb) {targets : List (Fin R)}
    (htargets : targets.Nodup) (hcontrol : ∀ r ∈ targets, control ≠ emb r)
    (f : Fin M → Fin 2) (r : Fin R) :
    (targets.foldl (fun h r' => controlledBitFlipMap control (emb r') h) f) (emb r) =
      if r ∈ targets then f (emb r) + f control else f (emb r) := by
  induction targets generalizing f with
  | nil => simp
  | cons r' rs ih =>
      have hr'nin : r' ∉ rs := (List.nodup_cons.mp htargets).1
      have hrs' : rs.Nodup := (List.nodup_cons.mp htargets).2
      have hcontrol_rs : ∀ r'' ∈ rs, control ≠ emb r'' :=
        fun r'' hr'' => hcontrol r'' (List.mem_cons_of_mem r' hr'')
      have hcontrol_ne_r' : control ≠ emb r' := hcontrol r' List.mem_cons_self
      rw [List.foldl_cons, ih hrs' hcontrol_rs]
      by_cases hrr : r = r'
      · subst hrr
        rw [controlledBitFlipMap_target control (emb r) f,
          controlledBitFlipMap_off control (emb r) f hcontrol_ne_r']
        simp [hr'nin]
      · have hne : emb r ≠ emb r' := fun h => hrr (hemb h)
        rw [controlledBitFlipMap_off control (emb r') f hne,
          controlledBitFlipMap_off control (emb r') f hcontrol_ne_r']
        by_cases hmem : r ∈ rs
        · simp [hmem, hrr]
        · simp [hmem, hrr]

/-! ## C11f.3 — The record-cat fanout circuit -/

/-- The controlled flip from `firstRecord R` to record site `r`, or a junk
identity gate when `r = 0` (never applied, since `nonFirstRecords R`
excludes `0`). -/
def catFanoutGate (R : ℕ) [NeZero R] (r : Fin R) : TwoLocalGate (R + 1) 2 :=
  if h : firstRecord R ≠ recordSite r then controlledBitFlipGate (firstRecord R) (recordSite r) h
  else ⟨LinearIsometryEquiv.refl ℂ (Sites (R + 1) 2), ∅, Circuit.isLocalTo_id_empty, by simp⟩

theorem catFanoutGate_eq_of_ne (R : ℕ) [NeZero R] {r : Fin R} (hr : r ≠ 0) :
    catFanoutGate R r =
      controlledBitFlipGate (firstRecord R) (recordSite r)
        (fun h => hr (recordSite_injective h).symm) := by
  unfold catFanoutGate
  rw [dif_pos]

/-- One controlled flip per non-first record site: copies the first
record's bit to every other record. -/
def recordCatFanoutCircuit (R : ℕ) [NeZero R] : Circuit (R + 1) 2 :=
  (nonFirstRecords R).map (catFanoutGate R)

@[simp] theorem recordCatFanoutCircuit_length (R : ℕ) [NeZero R] :
    (recordCatFanoutCircuit R).length = R - 1 := by
  simp [recordCatFanoutCircuit, Circuit.length, nonFirstRecords_length]

/-- Generic form: folding `catFanoutGate` over any list of non-first
(nonzero) record indices, as a circuit-eval statement on a basis vector. -/
private theorem eval_catFanout_list_configuration (R : ℕ) [NeZero R] (rs : List (Fin R))
    (hrs : ∀ r ∈ rs, r ≠ (0 : Fin R)) (f : Fin (R + 1) → Fin 2) :
    Circuit.eval (rs.map (catFanoutGate R)) (EuclideanSpace.single f (1 : ℂ)) =
      EuclideanSpace.single
        (rs.foldl (fun h r => controlledBitFlipMap (firstRecord R) (recordSite r) h) f) 1 := by
  induction rs generalizing f with
  | nil => rfl
  | cons r rs ih =>
      have hr : r ≠ (0 : Fin R) := hrs r List.mem_cons_self
      have hrs' : ∀ r' ∈ rs, r' ≠ (0 : Fin R) :=
        fun r' hr' => hrs r' (List.mem_cons_of_mem r hr')
      change Circuit.eval (rs.map (catFanoutGate R))
          ((catFanoutGate R r).unitary (EuclideanSpace.single f 1)) = _
      rw [catFanoutGate_eq_of_ne R hr]
      show Circuit.eval (rs.map (catFanoutGate R))
          (controlledBitFlipUnitary (firstRecord R) (recordSite r)
            (fun h => hr (recordSite_injective h).symm) (EuclideanSpace.single f 1)) = _
      rw [controlledBitFlipUnitary_single, ih hrs']
      rfl

private theorem eval_recordCatFanout_list_configuration (R : ℕ) [NeZero R]
    (f : Fin (R + 1) → Fin 2) :
    Circuit.eval ((nonFirstRecords R).map (catFanoutGate R))
        (EuclideanSpace.single f (1 : ℂ)) =
      EuclideanSpace.single
        ((nonFirstRecords R).foldl
          (fun h r => controlledBitFlipMap (firstRecord R) (recordSite r) h) f) 1 :=
  eval_catFanout_list_configuration R (nonFirstRecords R)
    (fun r hr => (mem_nonFirstRecords R r).mp hr) f

/-- Every site of `Fin (R + 1)` is either the first record, another record,
or the source. -/
private theorem eq_firstRecord_or_other (R : ℕ) [NeZero R] (s : Fin (R + 1)) :
    s = firstRecord R ∨ s = sourceSite R ∨ ∃ r : Fin R, r ≠ 0 ∧ s = recordSite r := by
  rcases eq_sourceSite_or_recordSite R s with hs | ⟨r, hs⟩
  · exact Or.inr (Or.inl hs)
  · by_cases hr : r = 0
    · exact Or.inl (hs.trans (by rw [hr]; rfl))
    · exact Or.inr (Or.inr ⟨r, hr, hs⟩)

theorem recordCatFanout_maps_configurationBranch (R : ℕ) [NeZero R] (f : Fin (R + 1) → Fin 2) :
    Circuit.evalOnH (recordCatFanoutCircuit R) (sitesEquivR (R + 1))
        (configurationBranch (R + 1) f) =
      configurationBranch (R + 1)
        (fun s => if s = firstRecord R then f s
          else if _h : ∃ r : Fin R, r ≠ 0 ∧ s = recordSite r then f s + f (firstRecord R)
          else f s) := by
  show Circuit.evalOnH (recordCatFanoutCircuit R) (sitesEquivR (R + 1))
      ((sitesEquivR (R + 1)).symm (EuclideanSpace.single f (1 : ℂ))) =
    (sitesEquivR (R + 1)).symm (EuclideanSpace.single
      (fun s => if s = firstRecord R then f s
        else if _h : ∃ r : Fin R, r ≠ 0 ∧ s = recordSite r then f s + f (firstRecord R)
        else f s) 1)
  apply (sitesEquivR (R + 1)).injective
  simp [Circuit.evalOnH]
  rw [recordCatFanoutCircuit, eval_recordCatFanout_list_configuration]
  congr 1
  funext s
  have hfirst_ne : ∀ r' ∈ nonFirstRecords R, firstRecord R ≠ recordSite r' :=
    fun r' hr' heq => (mem_nonFirstRecords R r').mp hr' (recordSite_injective heq.symm)
  rcases eq_firstRecord_or_other R s with hs | hs | ⟨r, hr, hs⟩
  · subst hs
    rw [foldl_controlledFlip_untouched_eq (firstRecord R) recordSite (nonFirstRecords R)
      (firstRecord R) hfirst_ne f]
    simp
  · subst hs
    have hnotex : ¬ ∃ r : Fin R, r ≠ 0 ∧ sourceSite R = recordSite r := by
      rintro ⟨r, -, hcontra⟩
      exact recordSite_ne_sourceSite r hcontra.symm
    rw [foldl_controlledFlip_untouched_eq (firstRecord R) recordSite (nonFirstRecords R)
      (sourceSite R) (fun r' _ => (recordSite_ne_sourceSite r').symm) f]
    simp [hnotex]
  · subst hs
    rw [foldl_controlledFlip_target_apply (firstRecord R) recordSite recordSite_injective
      (nonFirstRecords_nodup R) hfirst_ne f r]
    have hmem : r ∈ nonFirstRecords R := (mem_nonFirstRecords R r).mpr hr
    have hne_first : recordSite r ≠ firstRecord R := fun heq => hr (recordSite_injective heq)
    rw [if_pos hmem, if_neg hne_first, if_pos (⟨r, hr, rfl⟩ : ∃ r' : Fin R, r' ≠ 0 ∧
      recordSite r = recordSite r')]

/-! ## C11f.4 — Action on the blank-record and flipped-first-record basis states -/

/-- If a configuration's first-record bit is already `0`, the record-cat
fanout leaves it entirely unchanged: there is nothing to copy. -/
private theorem recordCatFanout_fixes_of_firstRecord_zero (R : ℕ) [NeZero R]
    (g : Fin (R + 1) → Fin 2) (hg0 : g (firstRecord R) = 0) :
    Circuit.evalOnH (recordCatFanoutCircuit R) (sitesEquivR (R + 1))
        (configurationBranch (R + 1) g) = configurationBranch (R + 1) g := by
  rw [recordCatFanout_maps_configurationBranch]
  congr 1
  funext s
  rcases eq_firstRecord_or_other R s with hs | hs | ⟨r, hr, hs⟩
  · subst hs
    rw [if_pos rfl]
  · subst hs
    have hnotfirst : sourceSite R ≠ firstRecord R := (recordSite_ne_sourceSite (0 : Fin R)).symm
    have hnotex : ¬ ∃ r : Fin R, r ≠ 0 ∧ sourceSite R = recordSite r := by
      rintro ⟨r, -, hcontra⟩
      exact recordSite_ne_sourceSite r hcontra.symm
    rw [if_neg hnotfirst, dif_neg hnotex]
  · subst hs
    have hnotfirst : recordSite r ≠ firstRecord R := fun heq => hr (recordSite_injective heq)
    have hex : ∃ r' : Fin R, r' ≠ 0 ∧ recordSite r = recordSite r' := ⟨r, hr, rfl⟩
    rw [if_neg hnotfirst, dif_pos hex, hg0, add_zero]

theorem recordCatFanout_maps_basis00 (R : ℕ) [NeZero R] :
    Circuit.evalOnH (recordCatFanoutCircuit R) (sitesEquivR (R + 1)) (basis00 R) = basis00 R :=
  recordCatFanout_fixes_of_firstRecord_zero R (config00 R) (config00_record R 0)

theorem recordCatFanout_maps_basis10 (R : ℕ) [NeZero R] :
    Circuit.evalOnH (recordCatFanoutCircuit R) (sitesEquivR (R + 1)) (basis10 R) = basis10 R :=
  recordCatFanout_fixes_of_firstRecord_zero R (config10 R) (config10_record R 0)

/-- After the profile-preparation gate flips the first record on top of
`config00` (source `0`, all records `0`), the record-cat fanout copies that
flipped bit to every other record, producing exactly `config01` (source `0`,
all records `1`). -/
theorem recordCatFanout_maps_flippedFirst_config00 (R : ℕ) [NeZero R] :
    Circuit.evalOnH (recordCatFanoutCircuit R) (sitesEquivR (R + 1))
        (configurationBranch (R + 1)
          (bitFlipConfigurationEquiv (R + 1) (firstRecord R) (config00 R))) =
      basis01 R := by
  rw [recordCatFanout_maps_configurationBranch]
  unfold basis01
  congr 1
  funext s
  rcases eq_firstRecord_or_other R s with hs | hs | ⟨r, hr, hs⟩
  · subst hs
    rw [if_pos rfl]
    show bitFlipConfigurationEquiv (R + 1) (firstRecord R) (config00 R) (firstRecord R) =
      config01 R (firstRecord R)
    rw [bitFlipConfigurationEquiv_at]
    show Equiv.swap (0 : Fin 2) 1 (config00 R (recordSite (0 : Fin R))) = config01 R (firstRecord R)
    rw [config00_record]
    show Equiv.swap (0 : Fin 2) 1 0 = config01 R (recordSite (0 : Fin R))
    rw [config01_record]
    decide
  · subst hs
    have hnotfirst : sourceSite R ≠ firstRecord R := (recordSite_ne_sourceSite (0 : Fin R)).symm
    have hnotex : ¬ ∃ r : Fin R, r ≠ 0 ∧ sourceSite R = recordSite r := by
      rintro ⟨r, -, hcontra⟩
      exact recordSite_ne_sourceSite r hcontra.symm
    rw [if_neg hnotfirst, dif_neg hnotex,
      bitFlipConfigurationEquiv_off _ _ _ _ hnotfirst, config00_source, config01_source]
  · subst hs
    have hnotfirst : recordSite r ≠ firstRecord R := fun heq => hr (recordSite_injective heq)
    have hex : ∃ r' : Fin R, r' ≠ 0 ∧ recordSite r = recordSite r' := ⟨r, hr, rfl⟩
    rw [if_neg hnotfirst, dif_pos hex,
      bitFlipConfigurationEquiv_off _ _ _ _ hnotfirst, config00_record]
    show (0 : Fin 2) +
        bitFlipConfigurationEquiv (R + 1) (firstRecord R) (config00 R) (firstRecord R) =
      config01 R (recordSite r)
    rw [bitFlipConfigurationEquiv_at]
    show (0 : Fin 2) + Equiv.swap (0 : Fin 2) 1 (config00 R (recordSite (0 : Fin R))) =
      config01 R (recordSite r)
    rw [config00_record, config01_record]
    decide

/-- After the profile-preparation gate flips the first record on top of
`config10` (source `1`, all records `0`), the record-cat fanout copies that
flipped bit to every other record, producing exactly `config11` (source `1`,
all records `1`). -/
theorem recordCatFanout_maps_flippedFirst_config10 (R : ℕ) [NeZero R] :
    Circuit.evalOnH (recordCatFanoutCircuit R) (sitesEquivR (R + 1))
        (configurationBranch (R + 1)
          (bitFlipConfigurationEquiv (R + 1) (firstRecord R) (config10 R))) =
      basis11 R := by
  rw [recordCatFanout_maps_configurationBranch]
  unfold basis11
  congr 1
  funext s
  rcases eq_firstRecord_or_other R s with hs | hs | ⟨r, hr, hs⟩
  · subst hs
    rw [if_pos rfl]
    show bitFlipConfigurationEquiv (R + 1) (firstRecord R) (config10 R) (firstRecord R) =
      config11 R (firstRecord R)
    rw [bitFlipConfigurationEquiv_at]
    show Equiv.swap (0 : Fin 2) 1 (config10 R (recordSite (0 : Fin R))) = config11 R (firstRecord R)
    rw [config10_record]
    show Equiv.swap (0 : Fin 2) 1 0 = config11 R (recordSite (0 : Fin R))
    rw [config11_record]
    decide
  · subst hs
    have hnotfirst : sourceSite R ≠ firstRecord R := (recordSite_ne_sourceSite (0 : Fin R)).symm
    have hnotex : ¬ ∃ r : Fin R, r ≠ 0 ∧ sourceSite R = recordSite r := by
      rintro ⟨r, -, hcontra⟩
      exact recordSite_ne_sourceSite r hcontra.symm
    rw [if_neg hnotfirst, dif_neg hnotex,
      bitFlipConfigurationEquiv_off _ _ _ _ hnotfirst, config10_source, config11_source]
  · subst hs
    have hnotfirst : recordSite r ≠ firstRecord R := fun heq => hr (recordSite_injective heq)
    have hex : ∃ r' : Fin R, r' ≠ 0 ∧ recordSite r = recordSite r' := ⟨r, hr, rfl⟩
    rw [if_neg hnotfirst, dif_pos hex,
      bitFlipConfigurationEquiv_off _ _ _ _ hnotfirst, config10_record]
    show (0 : Fin 2) +
        bitFlipConfigurationEquiv (R + 1) (firstRecord R) (config10 R) (firstRecord R) =
      config11 R (recordSite r)
    rw [bitFlipConfigurationEquiv_at]
    show (0 : Fin 2) + Equiv.swap (0 : Fin 2) 1 (config10 R (recordSite (0 : Fin R))) =
      config11 R (recordSite r)
    rw [config10_record, config11_record]
    decide

/-! ## C11f.5 — The record-cat preparation circuit -/

/-- Generic fact: evaluating an appended circuit is evaluating the first
part, then the second, through the same site identification. -/
private theorem evalOnH_append_apply {N d : ℕ} (C D : Circuit N d)
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (x : H (d ^ N)) :
    Circuit.evalOnH (C ++ D) e x = Circuit.evalOnH D e (Circuit.evalOnH C e x) := by
  simp [Circuit.evalOnH, Circuit.eval_append]

/-- The profile-preparation gate at the first record, followed by the
record-cat fanout onto every other record. -/
def recordCatPreparationCircuit (p : NoiseProfile) (R : ℕ) [NeZero R] : Circuit (R + 1) 2 :=
  [profilePreparationGate p R] ++ recordCatFanoutCircuit R

@[simp] theorem recordCatPreparationCircuit_length (p : NoiseProfile) (R : ℕ) [NeZero R] :
    (recordCatPreparationCircuit p R).length = R := by
  have hR := NeZero.pos R
  have hlen : List.length (recordCatFanoutCircuit R) = R - 1 := recordCatFanoutCircuit_length R
  show List.length ([profilePreparationGate p R] ++ recordCatFanoutCircuit R) = R
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- On blank records (`config00`), the record-cat preparation circuit
directly produces the noisy-zero-branch amplitude split between `basis00`
and `basis01`. -/
theorem recordCatPreparation_maps_basis00 (p : NoiseProfile) (R : ℕ) [NeZero R] :
    Circuit.evalOnH (recordCatPreparationCircuit p R) (sitesEquivR (R + 1)) (basis00 R) =
      p.keep • basis00 R + p.leak • basis01 R := by
  unfold recordCatPreparationCircuit
  rw [evalOnH_append_apply]
  show Circuit.evalOnH (recordCatFanoutCircuit R) (sitesEquivR (R + 1))
      (Circuit.evalOnH [profilePreparationGate p R] (sitesEquivR (R + 1)) (basis00 R)) = _
  rw [profilePreparationGate_maps_basis00, map_add, map_smul, map_smul,
    recordCatFanout_maps_basis00, recordCatFanout_maps_flippedFirst_config00]

/-- On blank records (`config10`), the record-cat preparation circuit
produces the intermediate `keep • basis10 + leak • basis11` split (the
`keep`/`leak` roles are exchanged relative to `noisyOneBranch`; the
subsequent `idealFanoutCircuit` step exchanges them back, cf.
`noisyMeasurement_maps_basis10`). -/
theorem recordCatPreparation_maps_basis10 (p : NoiseProfile) (R : ℕ) [NeZero R] :
    Circuit.evalOnH (recordCatPreparationCircuit p R) (sitesEquivR (R + 1)) (basis10 R) =
      p.keep • basis10 R + p.leak • basis11 R := by
  unfold recordCatPreparationCircuit
  rw [evalOnH_append_apply]
  show Circuit.evalOnH (recordCatFanoutCircuit R) (sitesEquivR (R + 1))
      (Circuit.evalOnH [profilePreparationGate p R] (sitesEquivR (R + 1)) (basis10 R)) = _
  rw [profilePreparationGate_maps_basis10, map_add, map_smul, map_smul,
    recordCatFanout_maps_basis10, recordCatFanout_maps_flippedFirst_config10]

#print axioms recordCatPreparation_maps_basis00
#print axioms recordCatPreparation_maps_basis10

end

end QuantumFoundations.Complexity.MeasurementGeneration
