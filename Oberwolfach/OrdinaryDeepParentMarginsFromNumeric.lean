module

public import Oberwolfach.OrdinaryDeepParentNumericHierarchy
public import Oberwolfach.OrdinaryEndpointDegreeFromInnerDensity

@[expose] public section
/-! Turn the preselected numerical hierarchy, actual domain proportions,
    bounded edits and parent balance into the deep-parent margin record. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
set_option synthInstance.maxSize 8192
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_deep_parent_margins_from_numeric
    (P F:SimpleGraph V) (A:Finset V) (Z:Finset U)
    (γ κ b B εf η κe p pR pH density tR tH L Ledit δ ε t K e a lam:ℝ)
    (num:OrdinaryDeepNumericParameters p κe a η εf K γ κ δ ε t lam b B)
    (hp:0<p) (hκe:0<κe) (hK:0<K) (hA:0<A.card)
    (hAfrac:a*Fintype.card V≤(A.card:ℝ))
    (hphysical:(Fintype.card (V⊕U):ℝ)≤K*A.card)
    (hZlo:κe*A.card≤(Z.card:ℝ)) (hZhi:Z.card≤A.card)
    (hpR:p≤pR) (hpR1:pR≤1) (hpH:p≤pH) (hpH1:pH≤1)
    (hL:0≤L) (hLsmall:L≤lam*A.card) (hLedit:0≤Ledit) (hLeditSmall:Ledit≤lam*A.card)
    (hF:∀v,(F.degree v:ℝ)≤L)
    (hparent:∀v,|pR*(A∩P.neighborFinset v).card-2*pH*Z.card|≤e)
    (hbalance:e≤δ*(2*Z.card*pH))
    (hthreshold:cycleThreshold 3≤density)
    (hmin:∀v,density*A.card≤((A∩P.neighborFinset v).card:ℝ))
    (hrow:tR≤ε*A.card/2) (hcolumn:tH≤ε*Z.card/2) :
    OrdinaryDeepParentMargins P F A Z γ κ b B εf η κe p pR pH density tR tH L Ledit δ ε t K e := by
  have ha:(0:ℝ)<A.card:=Nat.cast_pos.mpr hA
  have hn:(0:ℝ)≤Fintype.card V:=by positivity
  have hz:(0:ℝ)≤Z.card:=by positivity
  have hAupper:(A.card:ℝ)≤Fintype.card V:=by exact_mod_cast Finset.card_le_univ A
  have hεf:0≤εf:=num.lambda_pos.le.trans num.lambda_conflict
  have hC1:0≤(2*40+(1+2*40)/(2*κe*p):ℝ):=by positivity
  have hC2:0≤(10*(40/(κe*p^5)):ℝ):=by positivity
  have hLratio:L/A.card≤lam:=(div_le_iff₀ ha).2 (by simpa [mul_comm] using hLsmall)
  have hEratio:Ledit/A.card≤lam:=(div_le_iff₀ ha).2 (by simpa [mul_comm] using hLeditSmall)
  have hconflictScale:L≤εf*Fintype.card V:=by
    calc
      L≤lam*A.card:=hLsmall
      _≤εf*A.card:=mul_le_mul_of_nonneg_right num.lambda_conflict ha.le
      _≤εf*Fintype.card V:=mul_le_mul_of_nonneg_left hAupper hεf
  have hconflictInner:L≤(A.card:ℝ)/24:=by
    calc
      L≤lam*A.card:=hLsmall
      _≤(1/24:ℝ)*A.card:=mul_le_mul_of_nonneg_right num.lambda_inner ha.le
      _=(A.card:ℝ)/24:=by ring
  have hrowMargin:tR+4*Ledit≤ε*A.card:=by
    have h1:=mul_le_mul_of_nonneg_left hLeditSmall (show (0:ℝ)≤4 by norm_num)
    have h2:=mul_le_mul_of_nonneg_right num.lambda_row ha.le
    nlinarith only [hrow,h1,h2]
  have hindexMargin:tH+3*Ledit≤ε*Z.card:=by
    have h1:=mul_le_mul_of_nonneg_left hLeditSmall (show (0:ℝ)≤3 by norm_num)
    have h2:=mul_le_mul_of_nonneg_right num.lambda_index ha.le
    have h3:=mul_le_mul_of_nonneg_left hZlo num.epsilon_pos.le
    nlinarith only [hcolumn,h1,h2,h3]
  have hγ:γ*Fintype.card V≤(p^4/16)*A.card:=by
    have h1:=mul_le_mul_of_nonneg_right num.gamma_rim hn
    have h2:=mul_le_mul_of_nonneg_left hAfrac (show (0:ℝ)≤p^4/16 by positivity)
    nlinarith only [h1,h2]
  have hκ:κ*Fintype.card V≤(p^4/16)*A.card:=by
    have h1:=mul_le_mul_of_nonneg_right num.kappa_rim hn
    have h2:=mul_le_mul_of_nonneg_left hAfrac (show (0:ℝ)≤p^4/16 by positivity)
    nlinarith only [h1,h2]
  have hendpointScale:γ*Fintype.card (V⊕U)≤endpointCountCoefficient p κe*A.card:=by
    have h1:=mul_le_mul_of_nonneg_left hphysical num.gamma_pos.le
    have h2:=mul_le_mul_of_nonneg_right num.gamma_physical ha.le
    nlinarith only [h1,h2]
  have hendpointError:δ+(2*40+(1+2*40)/(2*κe*p))*L/A.card+
      (t+10*(40/(κe*p^5))*Ledit/A.card)≤η:=by
    have h1:(2*40+(1+2*40)/(2*κe*p))*L/A.card≤(2*40+(1+2*40)/(2*κe*p))*lam:=by
      convert mul_le_mul_of_nonneg_left hLratio hC1 using 1 <;> ring
    have h2:10*(40/(κe*p^5))*Ledit/A.card≤10*(40/(κe*p^5))*lam:=by
      convert mul_le_mul_of_nonneg_left hEratio hC2 using 1 <;> ring
    linarith only [h1,h2,num.endpoint_error]
  exact ⟨hA,hκe,hp,hL,hLedit,num.delta_pos.le,hZlo,hZhi,hpR,hpR1,hpH,hpH1,hF,hparent,hbalance,
    cycleThreshold_triangle_lower.trans hthreshold,hεf,hconflictScale,hconflictInner,hrowMargin,hindexMargin,
    num.count_error,hγ,hκ,hendpointScale,ordinary_endpoint_degree_from_inner_density P A density hthreshold hmin,
    hK.le,hphysical,hendpointError,num.lower_bound,num.upper_bound⟩
end Oberwolfach
