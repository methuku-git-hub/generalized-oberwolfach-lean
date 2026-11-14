module

public import Oberwolfach.OrdinaryRawReferenceRimDegrees
public import Oberwolfach.OrdinaryReferenceBalanceFromDegrees
public import Oberwolfach.RawOrdinaryDegreeCounts
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! A single ordinary reference sample has the approximate rim--spoke
    balance needed by the correction, with an explicit failure bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_raw_reference_balance_high_probability
    (P F:SimpleGraph V) (π:Equiv.Perm V) (p pH tR tH L:ℝ)
    (hp:0≤p) (hp1:p≤1) (htR:0≤tR) (htH:0<tH) (hU:0<Fintype.card U)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x k,0<k→k<2*d+1→(π^k) x≠x)
    (j:Color) (hj:∀u,s u j=pH)
    (hcentre:∀v,p*(P.degree v:ℝ)=2*(pH*Fintype.card U))
    (hF:∀v,(F.degree v:ℝ)≤L):
    1-(2*(Fintype.card V:ℝ)*Real.exp (-2*tR^2/Fintype.card V)+
      (Fintype.card V:ℝ)*(2*Real.exp (-2*tH^2/((4*(d:ℝ)+3)^2*Fintype.card U))))≤
      (FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀v,|(((rawWheelGraph P σ)\F).degree v:ℝ)-
        2*((Finset.univ.filter (fun u=>rawWheelSpokes π d σ j v u)).card:ℝ)|≤tR+2*tH+L):=by
  let μ:=FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS)
  let ER:=fun σ:RawWheelOutcome V U Γ Color=>∀v,|((rawWheelGraph P σ).degree v:ℝ)-p*(P.degree v:ℝ)|<tR
  let EH:=fun σ:RawWheelOutcome V U Γ Color=>∀v,
    |(Fintype.card {u:U // rawWheelSpokes π d σ j v u}:ℝ)-pH*Fintype.card U|<tH
  have hR:=ordinary_raw_reference_rim_degree_concentration P p tR hp hp1 htR d hd q hq hQ s hs hS
  have hH:=rawWheelSpokeDegrees_event π (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS hnoshort hU j pH hj tH htH
  have hh:=finiteLaw_intersection_lower μ ER EH
    (2*(Fintype.card V:ℝ)*Real.exp (-2*tR^2/Fintype.card V))
    ((Fintype.card V:ℝ)*(2*Real.exp (-2*tH^2/((4*(d:ℝ)+3)^2*Fintype.card U)))) hR hH
  rw [sub_add_eq_sub_sub]
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  apply ordinary_reference_balance_from_degrees (rawWheelGraph P σ) F (rawWheelSpokes π d σ j)
    (fun v=>p*(P.degree v:ℝ)) (pH*Fintype.card U) tR tH L hcentre
  · intro v;exact (hσ.1 v).le
  · intro v
    have hv:((Finset.univ.filter (fun u=>rawWheelSpokes π d σ j v u)).card:ℝ)=
        (Fintype.card {u:U // rawWheelSpokes π d σ j v u}:ℝ):=by
      congr 1
      exact (Fintype.card_subtype _).symm
    rw [hv]
    exact (hσ.2 v).le
  · exact hF
end Oberwolfach
