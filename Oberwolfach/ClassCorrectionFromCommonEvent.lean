module

public import Oberwolfach.ExpandedClassInitialBalance
public import Oberwolfach.ClassBalancedCorrection
public import Oberwolfach.SelectedRoutingFromClassEdits
public import Oberwolfach.ClassRoutingNumericalSupply

@[expose] public section
/-! The retained state-degree and two-path tests, together with regularisation
edits, yield the protected balanced class orientation and its bounded deletion. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem class_correction_from_common_event
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P S Protected:SimpleGraph V) (π:Equiv.Perm V) (d m L:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (mass:Fin 6→ℝ) (ρ D t b ε α p err f:ℝ)
    (hregular:S.IsRegularOfDegree (2*m)) (hn:0<Fintype.card V) (hL:0<L)
    (hρ:0≤ρ) (ht:0≤t) (hb:0≤b) (hε:0≤ε) (hα:0<α) (hp:0<p) (hf:0≤f)
    (hmass:(∑a∈({0,1,2,3,4}:Finset (Fin 6)),mass a)=ρ) (hsize:ρ*D=2*m)
    (hdegree:∀v,|(P.degree v:ℝ)-D|≤ε)
    (hcol:∀a v,|((∑w,sampledColourOrientation P (fun e=>σ (Sum.inl e)) a v w:ℕ):ℝ)-
      mass a/2*P.degree v|≤t)
    (hedit:∀v,((changed ((longPhysicalStateGraph P σ {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤b)
    (hprotected:∀x y,Protected.Adj x y→(S.Adj x y↔(longPhysicalStateGraph P σ {0,1,2,3,4}).Adj x y))
    (hforbid:∀v,(Protected.degree v:ℝ)≤f)
    (hmin:∀v,(1/2+α)*(Fintype.card V:ℝ)≤P.degree v)
    (htest:∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-err≤
      ((Finset.univ.filter (fun z=>
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false x z ∧
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false z y)).card:ℝ))
    (hsupply:err+2*b≤α*p^2*Fintype.card V)
    (hrouting:(Fintype.card V:ℝ)*(5*t+ρ/2*ε+b)/L+2*(5*t+ρ/2*ε+b)+4*L+2*f<α*p^2*Fintype.card V):
    ∃M:V→V→ℕ,
      (∀x y,M x y+M y x=if S.Adj x y then 1 else 0) ∧
      (∀v,(∑w,M v w)=m ∧ (∑w,M w v)=m) ∧
      (∀v,((orientationDisagreementGraph (longPhysicalStateGraph P σ {0,1,2,3,4})
        (fun e=>(σ (Sum.inl e)).2) M).degree v:ℝ)≤b+(5*t+ρ/2*ε+b)+2*L) ∧
      (∀x y,(orientationDisagreementGraph (longPhysicalStateGraph P σ {0,1,2,3,4})
        (fun e=>(σ (Sum.inl e)).2) M).Adj x y→¬Protected.Adj x y):=by
  let a:=5*t+ρ/2*ε+b
  let β:=α*p^2
  have ha:0≤a:=by dsimp [a];positivity
  have hβ:0<β:=by dsimp [β];positivity
  have herr:=expanded_class_initial_outdegree_error P S σ mass ρ D t b ε m hρ hmass hsize hdegree hcol hedit
  have hnum:=class_routing_numerical_supply P α p err b hmin hsupply
  have hpaths:=selected_routing_paths_from_class_edits P S π d σ p err b β hb hedit htest hnum
  exact class_balanced_correction (longPhysicalStateGraph P σ {0,1,2,3,4}) S Protected
    (fun e=>(σ (Sum.inl e)).2) m L hregular hL hn a f β b ha hf hβ hprotected hedit herr hforbid hpaths hrouting
end Oberwolfach
