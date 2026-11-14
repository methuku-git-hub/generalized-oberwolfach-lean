module

public import Oberwolfach.RawIntervalUnassignedPairColumn
public import Oberwolfach.MarkedExpandedRawLaw
public import Oberwolfach.FiniteProductProjection
public import Oberwolfach.FiniteLawSigmaProjection

@[expose] public section
/-! All distinct vertex pairs have many jointly unassigned hub labels, even
when their interval windows overlap. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem raw_unassigned_pairs_common_event (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (θ:ℝ) (hθ:0<θ) (hrem:∀u,θ≤1-(∑g,q u g)-(∑j,s u j))
    (hspace:1/(8*(d:ℝ))≤θ/2)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x) (t:ℝ) (ht:0≤t):
    1-2*(Fintype.card V:ℝ)^2*Real.exp (-2*t^2/Fintype.card U)≤
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
        (fun σ=>∀x y,x≠y→(5/32:ℝ)*θ^2*Fintype.card U-t≤
          rawIntervalUnassignedPairColumnCount π d σ x y Finset.univ):=by
  let μ:=FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  let I:={z:V×V // z.1≠z.2}
  have hsingle (z:I):μ.probability (fun σ=>
      rawIntervalUnassignedPairColumnCount π d σ z.1.1 z.1.2 Finset.univ < (5/32:ℝ)*θ^2*Fintype.card U-t)≤
        2*Real.exp (-2*t^2/Fintype.card U):=by
    let ν:=fun u=>rawIntervalCoordinateLaw (V:=V) d hd (q u) (hq u) (hQ u) (s u) (hs u) (hS u)
    let p:=fun u=>(FiniteLaw.pi (ν u)).probability (fun σ=>rawIntervalState π d σ z.1.1=none ∧ rawIntervalState π d σ z.1.2=none)
    have hp:∀u,(5/32:ℝ)*θ^2≤p u:=by
      intro u
      exact raw_interval_two_unassigned_probability_from_slack π d hd (q u) (hq u) (hQ u) (s u) (hs u) (hS u)
        θ hθ (hrem u) hspace hnoshort z.1.1 z.1.2 z.2
    have hsum:(5/32:ℝ)*θ^2*Fintype.card U≤∑u:U,p u:=by
      simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm] using
        (Finset.sum_le_sum (s:=Finset.univ) (fun u _=>hp u))
    have hh:=raw_interval_unassigned_pair_column_tail π d hd q hq hQ s hs hS z.1.1 z.1.2 Finset.univ t ht
    change μ.probability (fun σ=>t≤|rawIntervalUnassignedPairColumnCount π d σ z.1.1 z.1.2 Finset.univ-∑u,p u|)≤_ at hh
    apply (finiteLaw_probability_mono μ _ _ ?_).trans hh
    intro σ hbad
    have hneg:rawIntervalUnassignedPairColumnCount π d σ z.1.1 z.1.2 Finset.univ-∑u,p u≤-t:=by linarith
    exact le_trans (by linarith) (neg_le_abs _)
  have hh:=finiteLaw_common_event_lower μ (Finset.univ:Finset I)
    (fun z σ=>rawIntervalUnassignedPairColumnCount π d σ z.1.1 z.1.2 Finset.univ < (5/32:ℝ)*θ^2*Fintype.card U-t)
    (fun _=>2*Real.exp (-2*t^2/Fintype.card U)) (fun z _=>hsingle z)
  have hI:Fintype.card I≤Fintype.card V^2:=(Fintype.card_subtype_le _).trans_eq (by simp [pow_two])
  have hIR:(Fintype.card I:ℝ)≤(Fintype.card V:ℝ)^2:=by exact_mod_cast hI
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies,not_lt] at hh
  have hbudget:(Fintype.card I:ℝ)*(2*Real.exp (-2*t^2/Fintype.card U))≤
      2*(Fintype.card V:ℝ)^2*Real.exp (-2*t^2/Fintype.card U):=by
    nlinarith only [mul_le_mul_of_nonneg_right hIR (show 0≤2*Real.exp (-2*t^2/Fintype.card U) by positivity)]
  apply ((sub_le_sub_left hbudget 1).trans hh).trans
  apply finiteLaw_probability_mono
  intro σ hσ x y hxy
  exact hσ ⟨(x,y),hxy⟩
end Oberwolfach
