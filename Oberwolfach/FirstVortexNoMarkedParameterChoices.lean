module

public import Mathlib.Tactic

@[expose] public section
/-! Select the first-vortex matching, density and list parameters without
introducing a lower bound on the cycle parameter. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_no_marked_parameter_choices
    (b ρ₀ θ δold δglobal lamList βfinal C₀:ℝ)
    (hb:0<b) (hρ:0<ρ₀) (hθ:0<θ) (hδold:0<δold) (hδglobal:0<δglobal)
    (hlist:0<lamList) (hβfinal:0≤βfinal) (hβbound:βfinal≤lamList/4) (hC:1≤C₀):
    ∃αMatch εQ lam lamAssign:ℝ,
      0<αMatch ∧ (2*αMatch)/16≤b ∧
      (2*αMatch)/16≤((ρ₀/4)/40000)*θ/1024 ∧ 2*αMatch≤4*δglobal ∧
      0<εQ ∧ εQ≤δglobal ∧ βfinal+εQ≤lamList ∧
      εQ≤αMatch/(1000*C₀) ∧ εQ≤(ρ₀/4)/80000 ∧
      0<lam ∧ lam≤θ ∧ lam≤αMatch/128 ∧ lam≤δold*εQ/32 ∧
      lam<lamAssign :=by
  let target:=((ρ₀/4)/40000)*θ/1024
  have ht:0<target:=by dsimp [target]; positivity
  have hCpos:0<C₀:=by linarith
  let αMatch:=min (4*b) (min (4*target) δglobal)
  have hα:0<αMatch:=by dsimp [αMatch]; positivity
  have hαb:αMatch≤4*b:=min_le_left _ _
  have hαt:αMatch≤4*target:=le_trans (min_le_right _ _) (min_le_left _ _)
  have hαδ:αMatch≤δglobal:=le_trans (min_le_right _ _) (min_le_right _ _)
  let εQ:=min (δglobal/2) (min (lamList/2) (min (αMatch/(2000*C₀)) ((ρ₀/4)/160000)))
  have hε:0<εQ:=by dsimp [εQ]; positivity
  have hεδ:εQ≤δglobal/2:=min_le_left _ _
  have hεlist:εQ≤lamList/2:=le_trans (min_le_right _ _) (min_le_left _ _)
  have hεα:εQ≤αMatch/(2000*C₀):=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hερ:εQ≤(ρ₀/4)/160000:=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  let lam:=min (θ/2) (min (αMatch/256) (δold*εQ/64))
  have hlam:0<lam:=by dsimp [lam]; positivity
  have hlamθ:lam≤θ/2:=min_le_left _ _
  have hlamα:lam≤αMatch/256:=le_trans (min_le_right _ _) (min_le_left _ _)
  have hlamδ:lam≤δold*εQ/64:=le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨αMatch,εQ,lam,2*lam,hα,?_,?_,?_,hε,?_,?_,?_,?_,hlam,?_,?_,?_,?_⟩
  · linarith
  · dsimp [target] at hαt; linarith
  · linarith
  · linarith
  · linarith
  · have hden:αMatch/(2000*C₀)≤αMatch/(1000*C₀):=by
      apply div_le_div_of_nonneg_left hα.le (by positivity) (by nlinarith)
    exact hεα.trans hden
  · linarith
  · linarith
  · linarith
  · nlinarith
  · linarith
end Oberwolfach
