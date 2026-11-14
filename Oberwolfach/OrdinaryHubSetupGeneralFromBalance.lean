module

public import Oberwolfach.OrdinaryInnerHubWeightSetupGeneral
public import Oberwolfach.OrdinaryInnerParentConditions

@[expose] public section
/-! The fixed general-length hub-weight setup follows from the actual parent
    balance, induced conflict bound and the preselected cycle coefficients. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_hub_setup_general_from_balance
    (m:ℕ) (P F:SimpleGraph V) (A:Finset V) (Z:Finset U)
    (weight:OrdinaryCycle (P.induce (A:Set V)) (m+1)→ℝ)
    (p pR pH e δ ξ L cLo cHi b B η K:ℝ)
    (hA:0<A.card) (hp:0<p) (hp1:p≤1) (hpR:p≤pR) (hpR1:pR≤1) (hpH:p≤pH) (hpH1:pH≤1)
    (hδ:0≤δ) (hL:0≤L) (hcLo:0<cLo) (hcHi:0≤cHi) (hK:0≤K)
    (hparent:∀v,|pR*(P.neighborFinset v∩A).card-2*pH*Z.card|≤e)
    (hlo:pR*(A.card:ℝ)/2≤2*pH*Z.card) (hhi:2*pH*Z.card≤2*pR*A.card)
    (hreg:e/pR≤δ*A.card) (hF:∀v,(F.degree v:ℝ)≤L)
    (hweight:∀C,cLo/(A.card:ℝ)^(m-1)≤weight C ∧ weight C≤cHi/(A.card:ℝ)^(m-1))
    (hedge:∀x y,(∑C,if C.val.val.Adj x y then weight C else 0)=if (P.induce (A:Set V)).Adj x y then 1 else 0)
    (hsize:(Fintype.card V:ℝ)≤K*A.card) (hb:b≤cLo) (hB:(4*cHi/p^(3*m+1))*K^m≤B)
    (herr:ξ+2*δ+12*((m+1:ℕ):ℝ)^4*cHi*L/A.card≤η):
    OrdinaryInnerHubWeightSetupGeneral m P F A weight p pR pH (2*pH*Z.card/pR) δ ξ L cLo cHi b B η K:=by
  have hpRpos:0<pR:=hp.trans_le hpR
  have hcenter:=ordinary_induced_parent_degree_center_bounds A Z pR pH hpRpos hlo hhi
  have hregular:∀v:{x:V // x∈(A:Set V)},
      |(((P.induce (A:Set V)).degree v):ℝ)-2*pH*Z.card/pR|≤δ*A.card:=by
    intro v
    exact (ordinary_induced_parent_regularity_from_balance P A Z pR pH e hpRpos hparent v).trans hreg
  have hconf:=ordinary_induced_conflict_degree_from_ambient F A L hF
  exact ⟨hA,hp,hp1,hpR,hpR1,hpH,hpH1,hδ,hL,hcLo,hcHi,hK,
    hcenter.1,hcenter.2,hregular,hconf,hweight,hedge,hsize,hb,hB,herr⟩
end Oberwolfach
