module

public import Oberwolfach.OrdinaryPlacementTrackedCostBound
public import Oberwolfach.OrdinaryPlacementAfterSpacing

@[expose] public section
/-! The actual placement and matching rates yield the first-level edit
budget once their common cap is below the certificate tolerance. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem ordinary_placement_certificate_cost_bound
    (m d tAbs aAbs bAbs K N dNeed:ℕ) (η capEdit α lamList ζList δ θ κ b z matchErr σ κ' ζret lam a γ:ℝ)
    (hη:0<η) (hcap:capEdit≤η)
    (hstage:OrdinaryPlacementStage m dNeed α lamList ζList capEdit δ θ κ b z matchErr σ κ')
    (hafter:OrdinaryPlacementAfterSpacing m d N α δ θ κ b z matchErr ζret)
    (hmatching:OrdinaryPlacementMatchingRateBounds K θ κ' b z δ matchErr lam a γ):
    ∃Ncost:ℕ,∀n:ℕ,Ncost≤n→∀unused edit rows hubs:ℝ,
    unused≤2*θ→edit≤σ*n→
    rows+hubs≤((2^(tAbs*tAbs)*aAbs+2^(tAbs*tAbs)*bAbs:ℕ):ℝ)→
    let LF:ℝ:=2*((3*d:ℕ):ℝ)
    let newLoss:ℝ:=5*Real.sqrt δ*n
    let κref:ℝ:=(max a γ)*n+unused*n+3*(n:ℝ)^(3/5:ℝ)+((6*d+4:ℕ):ℝ)+b*n+LF
    let e:ℝ:=σ*n+2*(σ*n)+LF
    let Lrim:ℝ:=edit+κref+newLoss
    let Lspoke:ℝ:=max (2*newLoss+(Lrim+e)/2) (2*(δ*n)+σ*n);
    Lrim+Lspoke+rows+hubs≤14*η*n :=by
  obtain ⟨hδ,hδ1,_,hsqrt,hθ,_,hθδ,hκ,_,_,_,_,hσ,_,_,_,_,hb,_,hκ',hκ'κ,_⟩:=hstage
  obtain ⟨_,_,hsize,_⟩:=hafter
  obtain ⟨_,_,_,_,_,_,ha,hγ,_⟩:=hmatching
  exact ordinary_placement_tracked_cost_bound m d tAbs aAbs bAbs η δ θ κ κ' a γ b σ
    hη hδ hδ1 (hsqrt.trans hcap) hθ hθδ hκ hκ'κ ha hγ hb (hσ.trans hcap) hsize
end Oberwolfach
