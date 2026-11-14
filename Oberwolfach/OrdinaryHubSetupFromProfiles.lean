module

public import Oberwolfach.OrdinaryInnerHubWeightSetup
public import Oberwolfach.OrdinaryInnerParentConditions

@[expose] public section
/-! The fixed hub-weight setup follows from the deterministic parent density
and balance profiles, the chosen cycle weights, and displayed margins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_hub_setup_from_profiles
    (P F : SimpleGraph V) (A : Finset V) (Z : Finset U)
    (weight : OrdinaryCycle (P.induce (A : Set V)) 3 → ℝ)
    (density α p pR pH e δ ξ L cLo cHi b B η K : ℝ)
    (hA:0<A.card) (hp:0<p) (hp1:p≤1) (hpR:p≤pR) (hpR1:pR≤1) (hpH:p≤pH) (hpH1:pH≤1)
    (hδ:0≤δ) (hL:0≤L) (hcLo:0<cLo) (hcHi:0≤cHi) (hK:0≤K)
    (hthreshold:cycleThreshold 3+α≤density)
    (hmin:∀v,density*A.card≤((A∩P.neighborFinset v).card:ℝ))
    (hparent:∀v,|pR*(P.neighborFinset v∩A).card-2*pH*Z.card|≤e)
    (hlo:pR*(A.card:ℝ)/2≤2*pH*Z.card) (hhi:2*pH*Z.card≤2*pR*A.card)
    (hreg:e/pR≤δ*A.card) (hF:∀v,(F.degree v:ℝ)≤L)
    (hweight:∀C,cLo/(A.card:ℝ)≤weight C ∧ weight C≤cHi/(A.card:ℝ))
    (hedge:∀x y,(∑C,if C.val.val.Adj x y then weight C else 0)=if (P.induce (A:Set V)).Adj x y then 1 else 0)
    (hsize:(Fintype.card V:ℝ)≤K*A.card) (hb:b≤cLo) (hB:(4*cHi/p^7)*K^2≤B)
    (herr:ξ+2*δ+12*(3:ℝ)^4*cHi*L/A.card≤η) :
    OrdinaryInnerHubWeightSetup P F A weight p pR pH (2*pH*Z.card/pR) δ ξ L cLo cHi b B η K := by
  have hpRpos:0<pR:=hp.trans_le hpR
  have hh:=ordinary_inner_parent_conditions_from_profiles P F A Z density α pR pH e δ L hpRpos
    hthreshold hmin hparent hlo hhi hreg hF
  exact ⟨hA,hp,hp1,hpR,hpR1,hpH,hpH1,hδ,hL,hcLo,hcHi,hK,
    hh.2.1.1,hh.2.1.2,hh.2.2.1,hh.2.2.2,hweight,hedge,hsize,hb,hB,herr⟩
end Oberwolfach
