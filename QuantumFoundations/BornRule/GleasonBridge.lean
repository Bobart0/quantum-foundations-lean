import QuantumFoundations.BornRule.Perspective
import QuantumFoundations.Uhlhorn.GleasonExtend
import Gleason.Main

/-!
# B2 — Pont vers Gleason : élimination de l'axiome

Remplace l'`axiom`, nommé `gleason`, de l'ancien prototype (`tstar-born-rule-lean`,
`theorem1_general_en.lean`) par une vraie application de `Gleason.gleason`.

Écart favorable trouvé en reconnaissance par rapport au prototype : `g` est
construit directement sur `Proj1 n` via `Perspective.binary`, sans passer par
un `gline` vectoriel intermédiaire — la valeur ne dépend que de la droite
`(P : Submodule)`, jamais d'un représentant unitaire, donc rien ne force à
raisonner vecteur d'abord. Le lien avec U3a
(`exists_projMeasure_of_frameFunctionOnLines`) est alors immédiat : il suffit
de vérifier `IsFrameFunctionOnLines g` (positivité directe depuis (Pos),
somme-à-1 via `lemma4_noncontextual` + `basisPerspective`), puis d'appeler
`Gleason.gleason` (réel, pas axiomatisé) sur la `ProjMeasure` obtenue.
-/

namespace QuantumFoundations.BornRule

open scoped InnerProductSpace
open scoped Classical
open Gleason
open QuantumFoundations.Uhlhorn (Proj1 IsFrameFunctionOnLines
  exists_projMeasure_of_frameFunctionOnLines)

noncomputable section

variable {n : ℕ} (Est : Perspective n → Submodule ℂ (H n) → ℝ)

/-- `g P := Est (binary P) P` : la fonction-cadre sur les droites,
    directement sur `Proj1 n` — ne passe jamais par un `gline` vectoriel
    provisoire (écart favorable trouvé en reconnaissance par rapport au
    prototype, qui construisait `gline` en premier). Bien définie car la
    valeur ne dépend que de la droite `(P : Submodule)`, pas d'un
    représentant unitaire. -/
noncomputable def g (hn2 : 2 ≤ n) (P : Proj1 n) : ℝ :=
  Est (Perspective.binary (P : Submodule ℂ (H n))
        (fun h => by have := P.2; rw [h] at this; simp at this)
        (fun h => by
          have h1 : Module.finrank ℂ (P : Submodule ℂ (H n)) = n := by rw [h]; simp [finrank_top]
          have h2 := P.2
          omega))
      (P : Submodule ℂ (H n))

/-- **Lemme 5** : `g` est une fonction-cadre sur les droites au sens de
    U3a (`IsFrameFunctionOnLines`), sous (Grain), (Norm), (Pos). -/
theorem g_isFrameFunctionOnLines (hn2 : 2 ≤ n) (hA : AxGrain Est) (hN : AxNorm Est)
    (hPos : AxPos Est) : IsFrameFunctionOnLines (g Est hn2) := by
  constructor
  · intro P
    exact hPos _ _ (Finset.mem_insert_self _ _)
  · intro b
    have hterm : ∀ i, g Est hn2 (Proj1.mk_unit (b i) (b.norm_eq_one i))
        = Est (basisPerspective b) (ℂ ∙ (b i : H n)) := by
      intro i
      apply lemma4_noncontextual Est hA hN (Finset.mem_insert_self _ _)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    have hsum := hN (basisPerspective b)
    rwa [show (basisPerspective b).cells = Finset.univ.image (fun i => ℂ ∙ (b i : H n)) from rfl,
      Finset.sum_image (line_injective b)] at hsum

/-- **Théorème 1, Étape 1** : remplace intégralement l'`axiom` `gleason` et
    `exists_rho` de l'ancien fichier par une VRAIE application de
    `Gleason.gleason`, via U3a (`exists_projMeasure_of_frameFunctionOnLines`). -/
theorem exists_rho (hn3 : 3 ≤ n) (hA : AxGrain Est) (hN : AxNorm Est) (hPos : AxPos Est) :
    ∃ ρ : H n →ₗ[ℂ] H n, IsDensityOperator ρ ∧
      ∀ x : H n, ∀ hx : ‖x‖ = 1, g Est (by omega) (Proj1.mk_unit x hx) = (⟪ρ x, x⟫_ℂ).re := by
  obtain ⟨m, hm⟩ := exists_projMeasure_of_frameFunctionOnLines n (g Est (by omega))
    (g_isFrameFunctionOnLines Est (by omega) hA hN hPos)
  obtain ⟨ρ, ⟨hρ_dens, hρ_born⟩, -⟩ := Gleason.gleason hn3 m
  refine ⟨ρ, hρ_dens, fun x hx => ?_⟩
  have hPx : (Proj1.mk_unit x hx : Submodule ℂ (H n)) = ℂ ∙ x := rfl
  rw [← hm (Proj1.mk_unit x hx), hPx, hρ_born (ℂ ∙ x), bornValue_span_singleton ρ x hx]

end
end QuantumFoundations.BornRule
