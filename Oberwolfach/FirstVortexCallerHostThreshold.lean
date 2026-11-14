module

public import Oberwolfach.FirstVortexAllHubSmallLoadFromTests

@[expose] public section
/-! One host threshold simultaneously meets the final-density, square-root
and all-hub load requirements of the actual same-sample caller. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_caller_host_threshold
    (β δ θ:ℝ) (d:ℕ) (hβ:0<β) (hδ:0<δ) (hθ:0<θ)
    (hθδ:10*θ≤δ) (hspacing:1/(d:ℝ)≤θ/1024):
    ∃N:ℕ,∀n:ℕ,N≤n→0<n ∧ 100/β≤(n:ℝ) ∧ 200/β≤(n:ℝ) ∧
      2/Real.sqrt δ≤(n:ℝ) ∧
      Classical.choose (first_vortex_all_hub_small_load_from_tests δ θ d hδ hθ hθδ hspacing)≤n :=by
  let Nhub:=Classical.choose (first_vortex_all_hub_small_load_from_tests δ θ d hδ hθ hθδ hspacing)
  obtain ⟨Nβ,hNβ⟩:=exists_nat_gt (200/β)
  obtain ⟨Nδ,hNδ⟩:=exists_nat_gt (2/Real.sqrt δ)
  let N:=max 1 (max Nhub (max Nβ Nδ))
  refine ⟨N,?_⟩
  intro n hn
  have hn1:1≤n:=by dsimp [N] at hn;omega
  have hnhub:Nhub≤n:=by dsimp [N] at hn;omega
  have hnβ:Nβ≤n:=by dsimp [N] at hn;omega
  have hnδ:Nδ≤n:=by dsimp [N] at hn;omega
  have hnβ':(Nβ:ℝ)≤n:=by exact_mod_cast hnβ
  have hnδ':(Nδ:ℝ)≤n:=by exact_mod_cast hnδ
  have h200:200/β≤(n:ℝ):=le_of_lt (lt_of_lt_of_le hNβ hnβ')
  have h100:100/β≤(n:ℝ):=by
    exact (div_le_div_of_nonneg_right (by norm_num : (100:ℝ)≤200) hβ.le).trans h200
  have hroot:2/Real.sqrt δ≤(n:ℝ):=le_of_lt (lt_of_lt_of_le hNδ hnδ')
  exact ⟨by omega,h100,h200,hroot,hnhub⟩
end Oberwolfach
