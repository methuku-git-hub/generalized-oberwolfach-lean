module

public import Oberwolfach.OrdinaryPlacementStage
public import Oberwolfach.OrdinaryPlacementAfterSpacing
public import Oberwolfach.OrdinaryPlacementMatchingRateBounds

@[expose] public section
/-! The selected pre-sample placement hierarchy supplies the numerical
inequalities needed by the uniform edited-target embedding theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach

theorem ordinary_selected_placement_concrete_budgets
    (m d K N dNeed:ℕ)
    (α lamList ζList capEdit δ θ κ b z matchErr σ κ' ζret lam a γ:ℝ)
    (hstage:OrdinaryPlacementStage m dNeed α lamList ζList capEdit δ θ κ b z matchErr σ κ')
    (hafter:OrdinaryPlacementAfterSpacing m d N α δ θ κ b z matchErr ζret)
    (hmatching:OrdinaryPlacementMatchingRateBounds K θ κ' b z δ matchErr lam a γ):
    0<δ ∧ δ≤1 ∧ δ≤((lamList/2)/100)^2 ∧ 0<θ ∧ θ≤1/100 ∧ 0<ζret ∧
    0≤lam+γ*(1-θ+lam) ∧ lam+γ*(1-θ+lam)≤θ/8 ∧ max a γ≤κ ∧
    1/(8*(d:ℝ))+((m:ℝ)+1)*(d:ℝ)*ζret+(lam+γ*(1-θ+lam))≤(δ/8)/2 ∧
    2*θ+δ/8+((m:ℝ)+2)*κ≤δ ∧ 0≤b ∧
    16/(d:ℝ)+16*κ+16*b/α+4*z≤θ/8 ∧ b≤α/16 ∧ b≤δ/8 ∧
    ∀n:ℕ,N≤n→4/(d:ℝ)≤δ/16 ∧ 4*(n:ℝ)^(3/4:ℝ)≤δ*n/16 ∧ 2*((max a γ)*n)≤δ*n/8 :=by
  obtain ⟨hδ,hδ1,hδlist,hδcap,hθ,hθ1,hθδ,hκ,hb,hz,herr,hσ,hσcap,hbfloor,hzfloor,
    hbζ,hbα,hbδ,hzb,hκ',hκ'κ,hdNeed,hbudget,hrest⟩:=hstage
  obtain ⟨hζret,hcapacity,hsize,hret,hN,hpow⟩:=hafter
  obtain ⟨hlam,hlam1,ha,hγ,hlamθ,hγlam,haκ,hγκ,hab,haz,hγz,hγθ,haBound,
    hslack0,hslack8,hslackErr,hslack,hrows⟩:=hmatching
  have hmax:max a γ≤κ:=max_le (haκ.trans hκ'κ) (hγκ.trans hκ'κ)
  have hrate:1/(8*(d:ℝ))+((m:ℝ)+1)*(d:ℝ)*ζret+(lam+γ*(1-θ+lam))≤(δ/8)/2:=by linarith
  refine ⟨hδ,hδ1,hδlist,hθ,hθ1,hζret,hslack0,hslack8,hmax,hrate,hsize,hb.le,hcapacity,hbα,hbδ,?_⟩
  intro n hn
  exact ⟨(hpow n hn).1,(hpow n hn).2,hrows n⟩
end Oberwolfach
