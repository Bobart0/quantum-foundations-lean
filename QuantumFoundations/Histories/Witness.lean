import QuantumFoundations.Histories.Basic

/-!
# K2 — Witness : les deux ensembles cohérents de Kent

Données explicites en dimension 3 (`H 3`), vecteurs NON normalisés (décision de
conception de la reconnaissance : toute la contrariété se lit sur des rapports
où les normalisations `1/√3` s'annulent — éviter `Real.sqrt` partout où c'est
possible) :
* `ψ₀ := e₀+e₁+e₂` (préparation), `φ₀ := e₀+e₁−e₂` (post-sélection).
* `P i := ℂ∙(e i)` pour `i ∈ {0,1}` (les deux propositions mutuellement
  orthogonales, `P 0 ⟂ P 1` immédiat), `F := ℂ∙φ₀`.
* `S i := [Perspective.binary (P i), Perspective.binary F]`, famille cohérente
  à 2 étages pour chaque `i`.

## Écart vs la feuille de route : un seul but ouvert paramétré plutôt que deux

La route prévoyait deux buts ouverts distincts `S₁_consistent`/`S₂_consistent`,
tout en autorisant explicitement leur factorisation en un lemme paramétré par
`i` « si la duplication est lourde » (les deux preuves ne diffèrent que par
l'indice `i ∈ {0,1}` et l'annulation clé `⟪φ₀, e 1 + e 2⟫ = 0` /
`⟪φ₀, e 0 + e 2⟫ = 0`, structurellement identiques). Option retenue : un seul
`S_consistent (i : Fin 3)`, spécialisé en `S1_consistent`/`S2_consistent`
ci-dessous sans laisser de but supplémentaire ouvert. K2 ne compte donc qu'un
seul but ouvert physique (au lieu de deux), qui décharge néanmoins les deux
faits demandés par le plan.
-/

namespace QuantumFoundations.Histories

open scoped InnerProductSpace
open Gleason QuantumFoundations.BornRule

noncomputable section

/-- Base canonique (non normalisée en soi, mais chaque `e i` est unitaire) de
`H 3`. -/
def e (i : Fin 3) : H 3 := EuclideanSpace.single i (1 : ℂ)

theorem e_ne_zero (i : Fin 3) : e i ≠ 0 := by
  unfold e
  rw [Ne, PiLp.single_eq_zero_iff]
  norm_num

theorem e_ortho {i j : Fin 3} (hij : i ≠ j) : ⟪e i, e j⟫_ℂ = 0 := by
  unfold e
  rw [EuclideanSpace.inner_single_left]
  simp [hij]

/-- Préparation (non normalisée) : `ψ₀ := e₀+e₁+e₂`. -/
def ψ₀ : H 3 := e 0 + e 1 + e 2

/-- Post-sélection (non normalisée) : `φ₀ := e₀+e₁−e₂`. -/
def φ₀ : H 3 := e 0 + e 1 - e 2

theorem φ₀_inner_self : ⟪φ₀, φ₀⟫_ℂ = 3 := by
  unfold φ₀ e
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    EuclideanSpace.inner_single_left, map_one, PiLp.single_apply]
  norm_num [Fin.ext_iff]

theorem φ₀_ne_zero : φ₀ ≠ 0 := by
  intro h
  have := φ₀_inner_self
  rw [h] at this
  simp at this

/-- `P i := ℂ∙(e i)`, `i ∈ Fin 3` (seuls `i = 0, 1` servent au témoin). -/
def P (i : Fin 3) : Submodule ℂ (H 3) := ℂ ∙ (e i)

/-- Post-sélection : `F := ℂ∙φ₀`. -/
def F : Submodule ℂ (H 3) := ℂ ∙ φ₀

theorem P_ne_bot (i : Fin 3) : P i ≠ ⊥ := by
  unfold P; rw [Submodule.ne_bot_iff]
  exact ⟨e i, Submodule.mem_span_singleton_self _, e_ne_zero i⟩

theorem P_ne_top (i : Fin 3) : P i ≠ ⊤ := by
  unfold P
  intro htop
  have h1 : Module.finrank ℂ (ℂ ∙ (e i)) = 1 := finrank_span_singleton (e_ne_zero i)
  rw [htop, finrank_top] at h1
  simp at h1

theorem F_ne_bot : F ≠ ⊥ := by
  unfold F; rw [Submodule.ne_bot_iff]
  exact ⟨φ₀, Submodule.mem_span_singleton_self _, φ₀_ne_zero⟩

theorem F_ne_top : F ≠ ⊤ := by
  unfold F
  intro htop
  have h1 : Module.finrank ℂ (ℂ ∙ φ₀) = 1 := finrank_span_singleton φ₀_ne_zero
  rw [htop, finrank_top] at h1
  simp at h1

/-- Les deux propositions du témoin de Kent sont mutuellement orthogonales
(immédiat : `e 0 ⊥ e 1`). -/
theorem P_ortho {i j : Fin 3} (hij : i ≠ j) : P i ⟂ P j := by
  unfold P
  rw [Submodule.isOrtho_iff_le]
  intro x hx
  rw [Submodule.mem_orthogonal]
  intro y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [inner_smul_left, inner_smul_right, e_ortho hij.symm]
  ring

/-- Étage initial `i` : perspective binaire `{P i, (P i)ᗮ}`. -/
def Dstage (i : Fin 3) : Perspective 3 := Perspective.binary (P i) (P_ne_bot i) (P_ne_top i)

/-- Étage final (post-sélection) : perspective binaire `{F, Fᗮ}`. -/
def DF : Perspective 3 := Perspective.binary F F_ne_bot F_ne_top

/-- Famille à 2 étages `Sᵢ := [{P i, (P i)ᗮ}, {F, Fᗮ}]`. -/
def S (i : Fin 3) : Fin 2 → Perspective 3 := ![Dstage i, DF]

/-- **K2, but ouvert unique.** `Sᵢ` est cohérente pour `ψ₀`, pour `i ∈ {0,1}` (les
deux seuls cas utilisés par le témoin). Par `decFunctional_last_stage_orthogonal`
(K1(a)), seules les paires d'histoires différant à l'étage `0` restent à
examiner ; l'annulation clé est `⟪φ₀, projL (P i)ᗮ ψ₀⟫ = 0` (calcul explicite
sur `H 3`, à retrouver via `Fin.sum_univ_three`/`EuclideanSpace.inner_single_left`,
voir reconnaissance A.3). -/
theorem S_consistent (i : Fin 3) : IsConsistent ψ₀ (S i) := by
  sorry

/-- `S1 := S 0` : famille cohérente construite sur `P 0`. -/
theorem S1_consistent : IsConsistent ψ₀ (S 0) := S_consistent 0

/-- `S2 := S 1` : famille cohérente construite sur `P 1`. -/
theorem S2_consistent : IsConsistent ψ₀ (S 1) := S_consistent 1

end
end QuantumFoundations.Histories
