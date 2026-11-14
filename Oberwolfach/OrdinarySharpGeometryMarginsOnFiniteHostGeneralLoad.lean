module

public import Oberwolfach.OrdinarySharpGeometryMarginsOnFiniteHost

@[expose] public section
/-! Instantiate the sharp balance and edit inequalities on the actual
finite parent and its two protected root sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_sharp_geometry_margins_on_finite_host_general_load
    (m loadK:ℕ) (I T:Finset V) (W:Finset U) (q β εR εH conflict deepCost ξ κ η ηInitial γ edit lam:ℝ)
    (hU:Fintype.card U≤Fintype.card V)
    (hq:0≤q) (hq1:q≤1) (hβ:0≤β) (hεR:0≤εR) (hεH:0≤εH)
    (hconf:0≤conflict) (hdeep:0≤deepCost) (hξ:0≤ξ) (hκ:0≤κ) (hη:0≤η) (hηI:0≤ηInitial)
    (hγ:0≤γ) (hedit:0<edit) (hlam:0≤lam) (hlam1:lam≤1/4)
    (hβcap:β≤γ/1000) (hRcap:εR≤γ/1000) (hHcap:εH≤γ/1000)
    (hconfCap:conflict≤(γ/1000)*Fintype.card V) (hξcap:ξ≤γ/160000) (hκcap:κ≤γ/1000)
    (hηcap:η≤γ/1000) (hηIcap:ηInitial≤η) (hdeepCap:deepCost≤10*ξ*Fintype.card V)
    (hroots:(T.card:ℝ)+W.card≤lam*Fintype.card V)
    (hrow:3*(((loadK:ℝ)+1)*lam)≤edit/4) (hlevel:lam*((m:ℝ)+1)≤edit/4)
    (hκedit:κ≤edit/(72*((m:ℝ)+2))):
    let A:=Finset.univ\T;
    let deep:=q*β*T.card+εR*T.card+2*(εH*W.card)+conflict+2*deepCost;
    let cover:=10*ξ*I.card;let loss:=12*κ*Fintype.card V;
    let bin:=η*I.card;let cin:=ηInitial*I.card+2*deepCost;
    let ell:=max (18*κ*Fintype.card V+3*((W.card:ℝ)+((loadK:ℝ)+1)*T.card))
      (3*κ*Fintype.card V*((m:ℝ)+1)+(T.card:ℝ)*((m:ℝ)+1));
    0≤deep ∧ 0≤bin ∧ 0≤cin ∧
    deep+2*cover≤γ*Fintype.card A ∧ bin+deep+4*cover≤γ*Fintype.card A ∧
    cin+deep+loss≤γ*Fintype.card A ∧ ell≤edit*Fintype.card A:=by
  intro A deep cover loss bin cin ell
  have hK0:(0:ℝ)≤loadK:=by positivity
  have hrow0:3*lam≤edit/4:=by nlinarith [mul_nonneg hK0 hlam]
  have hbase:=ordinary_sharp_geometry_margins_on_finite_host m I T W q β εR εH conflict deepCost ξ κ η ηInitial γ edit lam
    hU hq hq1 hβ hεR hεH hconf hdeep hξ hκ hη hηI hγ hedit hlam hlam1 hβcap hRcap hHcap
    hconfCap hξcap hκcap hηcap hηIcap hdeepCap hroots hrow0 hlevel hκedit
  obtain ⟨hdeep0,hbin,hcin,hfirst,hsecond,hthird,hellOld⟩:=hbase
  have hn:0≤(Fintype.card V:ℝ):=by positivity
  have hW0:0≤(W.card:ℝ):=by positivity
  have hA:Fintype.card A+T.card=Fintype.card V:=by
    simpa only [Fintype.card_coe,Finset.card_univ] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
  have hAr:(Fintype.card A:ℝ)+T.card=Fintype.card V:=by exact_mod_cast hA
  have hhalf:(Fintype.card V:ℝ)/2≤Fintype.card A:=by
    have hh:=mul_le_mul_of_nonneg_right hlam1 hn
    linarith only [hroots,hW0,hAr,hh]
  have hweighted:(W.card:ℝ)+((loadK:ℝ)+1)*T.card≤((loadK:ℝ)+1)*lam*Fintype.card V:=by
    have hh:=mul_le_mul_of_nonneg_left hroots (show (0:ℝ)≤(loadK:ℝ)+1 by positivity)
    nlinarith [mul_nonneg hK0 hW0]
  have hden:0<72*((m:ℝ)+2):=by positivity
  have hκmul:κ*(72*((m:ℝ)+2))≤edit:=(le_div_iff₀ hden).mp hκedit
  have hm0:(0:ℝ)≤m:=by positivity
  have hκsmall:18*κ≤edit/4:=by nlinarith [mul_nonneg hm0 hκ]
  have hκn:=mul_le_mul_of_nonneg_right hκsmall hn
  have hrown:=mul_le_mul_of_nonneg_right hrow hn
  have hhalfedit:=mul_le_mul_of_nonneg_left hhalf hedit.le
  have hfirstEll:18*κ*Fintype.card V+3*((W.card:ℝ)+((loadK:ℝ)+1)*T.card)≤edit*Fintype.card A:=by
    nlinarith only [hweighted,hκn,hrown,hhalfedit]
  have hsecondEll:3*κ*Fintype.card V*((m:ℝ)+1)+(T.card:ℝ)*((m:ℝ)+1)≤edit*Fintype.card A:=by
    exact (le_max_right _ _).trans hellOld
  exact ⟨hdeep0,hbin,hcin,hfirst,hsecond,hthird,max_le hfirstEll hsecondEll⟩
end Oberwolfach
