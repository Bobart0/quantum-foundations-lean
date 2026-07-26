import QuantumFoundations.ProbabilityAPI

/-!
**FR.** # Audit de régression pour l'API destinée aux développements aval

Module non importé par la racine (à l'image de `Audit/FoP.lean`), exécuté
séparément en CI. Il exerce chaque wrapper ajouté par le jalon « API amont
pour `everettian-probability-lean` » via un `example` intégralement prouvé,
puis imprime les axiomes de chaque nouvelle déclaration. Objectif : un
futur refactor qui casserait un contrat consommé en aval échoue ici, dans
ce dépôt, plutôt que dans le dépôt aval.

**EN.** # Regression audit for the downstream-facing API

A module not imported by the root (mirroring `Audit/FoP.lean`), run
separately in CI. It exercises every wrapper added by the "upstream API for
`everettian-probability-lean`" milestone via a fully proved `example`, then
prints the axioms of every new declaration. Goal: a future refactor that
would break a downstream-consumed contract fails here, in this repository,
rather than in the downstream one.
-/

namespace QuantumFoundations.Audit.DownstreamAPI

open QuantumFoundations
open QuantumFoundations.BornRule
open QuantumFoundations.ProbabilityAPI.BornBridge
open scoped InnerProductSpace Classical
open Gleason

noncomputable section

/-! ## A concrete binary perspective on `H 2` -/

private def e0 : H 2 := EuclideanSpace.single 0 1
private def e1 : H 2 := EuclideanSpace.single 1 1

private def K : Submodule ℂ (H 2) := ℂ ∙ e0

private theorem K_ne_bot : K ≠ ⊥ := by simp [K, e0]

private theorem e1_not_mem_K : e1 ∉ K := by
  rw [K, Submodule.mem_span_singleton]
  rintro ⟨a, ha⟩
  have h1 : (e1 : H 2) 1 = (a • e0 : H 2) 1 := by rw [ha]
  simp [e0, e1] at h1

private theorem K_ne_top : K ≠ ⊤ := by
  intro h
  apply e1_not_mem_K
  rw [h]
  trivial

private noncomputable def Dfine : Perspective 2 := Perspective.binary K K_ne_bot K_ne_top

private theorem K_mem_Dfine : K ∈ Dfine.cells := by
  show K ∈ ({K, Kᗮ} : Finset (Submodule ℂ (H 2)))
  simp

/-! ## Nonvacuity witnesses re-exported under `ProbabilityAPI.BornRule` -/

open QuantumFoundations.ProbabilityAPI.BornRule

example {n : ℕ} (v : H n) (hv : ‖v‖ = 1) : AxGrain (E₀ v) :=
  (E₀_satisfies_axioms v hv).1

example : (Dfine.cells.filter (· ≤ K)).sup id = K :=
  refine_filter_sup_eq Dfine Dfine (Refines.refl Dfine) K K_mem_Dfine

/-! ## QB8.1 — Mandated end-to-end example (`grainCoherenceTheorem_projector`) -/

example {n : ℕ} (Est : Perspective n → Submodule ℂ (H n) → ℝ)
    (hn3 : 3 ≤ n) (hA : AxGrain Est) (hN : AxNorm Est) (hPos : AxPos Est)
    {v : H n} (hv : ‖v‖ = 1) (hNul : AxNul Est v)
    (D : Perspective n) {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) :
    Est D c = ‖projL c v‖ ^ 2 :=
  grainCoherenceTheorem_projector Est hn3 hA hN hPos hv hNul D hc

/-! ## `Refines.refl` and `Refines.trans` (projective side) -/

example : Refines Dfine Dfine := Refines.refl Dfine

example : Refines Dfine Dfine :=
  Refines.trans (Refines.refl Dfine) (Refines.refl Dfine)

/-! ## `parentOf` and its specification lemmas -/

example : parentOf (Refines.refl Dfine) K ∈ Dfine.cells :=
  parentOf_mem (Refines.refl Dfine) K_mem_Dfine

example : K ≤ parentOf (Refines.refl Dfine) K :=
  parentOf_le (Refines.refl Dfine) K_mem_Dfine

/-! ## Chained example: `Refines.trans`, `parentOf`, `parentOf_eq_of_le`,
`coarseCells_eq_fiber_parentOf` on the concrete binary perspective `Dfine` -/

example :
    parentOf (Refines.trans (Refines.refl Dfine) (Refines.refl Dfine)) K = K :=
  parentOf_eq_of_le _ K_mem_Dfine K_mem_Dfine (le_refl K)

example :
    coarseCells Dfine K
      = Dfine.cells.filter
          (fun c' => parentOf (Refines.trans (Refines.refl Dfine) (Refines.refl Dfine)) c' = K) :=
  coarseCells_eq_fiber_parentOf (Refines.trans (Refines.refl Dfine) (Refines.refl Dfine)) K_mem_Dfine

/-! ## `coarseCells` and `axGrain_iff_coarseCells` -/

example (D' : Perspective 2) (c c' : Submodule ℂ (H 2)) :
    c' ∈ coarseCells D' c ↔ c' ∈ D'.cells ∧ c' ≤ c :=
  mem_coarseCells_iff D' c c'

example (Est : Perspective 2 → Submodule ℂ (H 2) → ℝ) :
    AxGrain Est ↔ ∀ D' D : Perspective 2, Refines D' D → ∀ c ∈ D.cells,
      Est D c = ∑ c' ∈ coarseCells D' c, Est D' c' :=
  axGrain_iff_coarseCells Est

/-! ## `EffectPerspectives.Refines.trans` -/

example {n : ℕ} {fine mid coarse : EffectPerspectives.EffectPerspective n} :
    EffectPerspectives.Refines fine mid → EffectPerspectives.Refines mid coarse →
      EffectPerspectives.Refines fine coarse :=
  EffectPerspectives.Refines.trans

/-! ## `BornBridge`'s re-exported record-induced Born theorem -/

example {n K R A : ℕ} [NeZero R] [NeZero K]
    (Obs : Fin A → Fin R → QuantumFoundations.BranchesRiedel.LabeledResolution n K)
    (ψ : H n) (hψ : ‖ψ‖ = 1)
    (hrec : ∀ a, QuantumFoundations.BranchesRiedel.IsRecordedOn ψ (Obs a))
    (hcw : QuantumFoundations.BranchesRiedel.CommuteWitness Obs)
    (Est : Perspective n → Submodule ℂ (H n) → ℝ) (hn3 : 3 ≤ n)
    (hA : AxGrain Est) (hN : AxNorm Est) (hPos : AxPos Est) (hNul : AxNul Est ψ) :
    Nonempty (RecordInducedBornConclusion Obs ψ Est) :=
  record_induced_Born_decomposition Obs ψ hψ hrec hcw Est hn3 hA hN hPos hNul

end

/-! ## Axiom audit: every declaration added by this milestone -/

#print axioms QuantumFoundations.BornRule.Refines.refl
#print axioms QuantumFoundations.BornRule.Refines.trans
#print axioms QuantumFoundations.BornRule.parentOf
#print axioms QuantumFoundations.BornRule.parentOf_mem
#print axioms QuantumFoundations.BornRule.parentOf_le
#print axioms QuantumFoundations.BornRule.parentOf_eq_of_le
#print axioms QuantumFoundations.BornRule.coarseCells
#print axioms QuantumFoundations.BornRule.mem_coarseCells_iff
#print axioms QuantumFoundations.BornRule.axGrain_iff_coarseCells
#print axioms QuantumFoundations.BornRule.coarseCells_eq_fiber_parentOf
#print axioms QuantumFoundations.BornRule.EffectPerspectives.Refines.trans
#print axioms QuantumFoundations.BornRule.refine_filter_sup_eq
#print axioms QuantumFoundations.BornRule.E₀_satisfies_axioms

end QuantumFoundations.Audit.DownstreamAPI
