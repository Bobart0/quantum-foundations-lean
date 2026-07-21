import QuantumFoundations.BornRule.Perspective
import QuantumFoundations.Uhlhorn.GleasonExtend
import Gleason.Main

/-!
**FR.** # B2 — Pont vers Gleason

Construit une densité `ρ` à partir d'une règle d'estimation `Est` satisfaisant
(Grain), (Norm), (Pos), via une vraie application du théorème de Gleason
(`Gleason.gleason`, dépendance externe épinglée).

`g : Proj1 n → ℝ` est construit directement sur `Proj1 n` via
`Perspective.binary`, sans passer par un intermédiaire vectoriel — la valeur
ne dépend que de la droite `(P : Submodule)`, jamais d'un représentant
unitaire, donc rien ne force à raisonner vecteur d'abord. Le lien avec U3a
(`exists_projMeasure_of_frameFunctionOnLines`) est alors immédiat : il suffit
de vérifier `IsFrameFunctionOnLines g` (positivité directe depuis (Pos),
somme-à-1 via `lemma4_noncontextual` + `basisPerspective`), puis d'appeler
`Gleason.gleason` (réel, pas axiomatisé) sur la `ProjMeasure` obtenue.

**EN.** # B2 — Bridge to Gleason

Constructs a density operator ρ from an estimation rule Est satisfying
(Grain), (Norm), and (Pos), through a genuine application of Gleason's theorem
(Gleason.gleason, pinned external dependency).

g : Proj1 n → ℝ is constructed directly on Proj1 n via
Perspective.binary, without passing through an intermediate vector-valued
representation—the value depends only on the line (P : Submodule), never on
a unit representative, so there is no need to reason with vectors first.
The connection to U3a (exists_projMeasure_of_frameFunctionOnLines) is then
immediate: it suffices to verify IsFrameFunctionOnLines g (positivity
directly from (Pos), sum-to-one via lemma4_noncontextual +
basisPerspective), and then apply Gleason.gleason (an actual theorem, not
axiomatized) to the resulting ProjMeasure.
-/

namespace QuantumFoundations.BornRule

open scoped InnerProductSpace
open scoped Classical
open Gleason
open QuantumFoundations.Uhlhorn (Proj1 IsFrameFunctionOnLines
  exists_projMeasure_of_frameFunctionOnLines)

noncomputable section

variable {n : ℕ} (Est : Perspective n → Submodule ℂ (H n) → ℝ)

/--
**FR.** `g P := Est (binary P) P` : la fonction-cadre sur les droites, définie
    directement sur `Proj1 n`, sans intermédiaire vectoriel. Bien définie car
    la valeur ne dépend que de la droite `(P : Submodule)`, pas d'un
    représentant unitaire.

**EN.** g P := Est (binary P) P: the frame function on lines, defined
 directly on Proj1 n, without an intermediate vector representation. It
 is well-defined because the value depends only on the line
 (P : Submodule), not on a unit representative.
-/
noncomputable def g (hn2 : 2 ≤ n) (P : Proj1 n) : ℝ :=
  Est (Perspective.binary (P : Submodule ℂ (H n))
        (fun h => by have := P.2; rw [h] at this; simp at this)
        (fun h => by
          have h1 : Module.finrank ℂ (P : Submodule ℂ (H n)) = n := by rw [h]; simp [finrank_top]
          have h2 := P.2
          omega))
      (P : Submodule ℂ (H n))

/--
**FR.** **Lemme 5** : `g` est une fonction-cadre sur les droites au sens de
    U3a (`IsFrameFunctionOnLines`), sous (Grain), (Norm), (Pos).

**EN.** Lemma 5: g is a frame function on lines in the sense of
 U3a (IsFrameFunctionOnLines), under (Grain), (Norm), and (Pos).
-/
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

/--
**FR.** Une règle d'estimation satisfaisant (Grain), (Norm), (Pos) est représentée
    par un opérateur densité `ρ` via la règle de Born, sur tout vecteur
    unitaire — VRAIE application de `Gleason.gleason` sur la `ProjMeasure`
    obtenue via U3a (`exists_projMeasure_of_frameFunctionOnLines`).

**EN.** An estimation rule satisfying (Grain), (Norm), and (Pos) is represented
 by a density operator ρ through the Born rule on every unit vector—a
 GENUINE application of Gleason.gleason to the ProjMeasure obtained via
 U3a (exists_projMeasure_of_frameFunctionOnLines).
-/
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
