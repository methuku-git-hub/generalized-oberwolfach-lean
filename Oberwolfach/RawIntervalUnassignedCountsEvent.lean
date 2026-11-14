module

public import Oberwolfach.RawIntervalUnassignedHubRestricted
public import Oberwolfach.RawIntervalUnassignedColumnCount
public import Oberwolfach.MarkedExpandedRawLaw
public import Oberwolfach.FiniteProductProjection
public import Oberwolfach.FiniteLawSigmaProjection

@[expose] public section
/-! Simultaneous unassigned counts on fixed vertex and hub domains, projected
from the full retained exposure. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem raw_interval_unassigned_fixed_domains_event (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hn:0<Fintype.card V) (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (A:Finset V) (J:Finset U) (t:ℝ) (ht:0<t):
    1-2*Fintype.card U*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V:ℝ)))-
      2*Fintype.card V*Real.exp (-2*t^2/J.card)≤
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability (fun σ=>
      (∀ u,|rawIntervalUnassignedHubCountOn π d σ u A-(A.card:ℝ)*(1-(∑ g,q u g)-(∑ j,s u j))|<t) ∧
      (∀ v,|rawIntervalUnassignedColumnCount π d σ v J-∑ u∈J,(1-(∑ g,q u g)-(∑ j,s u j))|<t)) := by
  let μ:=FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  let Er:=fun (σ:RawIntervalFamilyOutcome V U Γ Color)=>∀ u,|rawIntervalUnassignedHubCountOn π d σ u A-(A.card:ℝ)*(1-(∑ g,q u g)-(∑ j,s u j))|<t
  let Ec:=fun (σ:RawIntervalFamilyOutcome V U Γ Color)=>∀ v,|rawIntervalUnassignedColumnCount π d σ v J-∑ u∈J,(1-(∑ g,q u g)-(∑ j,s u j))|<t
  have hr:=finiteLaw_common_event_lower μ (Finset.univ:Finset U)
    (fun u σ=>t≤|rawIntervalUnassignedHubCountOn π d σ u A-(A.card:ℝ)*(1-(∑ g,q u g)-(∑ j,s u j))|)
    (fun _=>2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V:ℝ))))
    (fun u _=>by
      have hh:=rawIntervalUnassignedHubCountOn_tail π d hd q hq hQ s hs hS hn u A t ht
      rw [rawIntervalUnassignedHubCountOn_expectation π d hd q hq hQ s hs hS hnoshort u A] at hh
      exact hh)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies,not_le] at hr
  have hr':1-2*Fintype.card U*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V:ℝ)))≤μ.probability Er:=by
    dsimp [Er];convert hr using 1 <;> ring
  have hc:=finiteLaw_common_event_lower μ (Finset.univ:Finset V)
    (fun v σ=>t≤|rawIntervalUnassignedColumnCount π d σ v J-∑ u∈J,(1-(∑ g,q u g)-(∑ j,s u j))|)
    (fun _=>2*Real.exp (-2*t^2/J.card))
    (fun v _=>rawIntervalUnassignedColumnCount_tail π d hd q hq hQ s hs hS hnoshort v J t ht.le)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies,not_le] at hc
  have hc':1-2*Fintype.card V*Real.exp (-2*t^2/J.card)≤μ.probability Ec:=by
    dsimp [Ec];convert hc using 1 <;> ring
  have hj:=finiteLaw_good_intersection μ Er Ec (2*Fintype.card V*Real.exp (-2*t^2/J.card)) hc'
  exact (sub_le_sub_right hr' _).trans hj
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem raw_expanded_unassigned_fixed_domains_event (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hn:0<Fintype.card V) (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a))
    (A:Finset V) (J:Finset U) (t:ℝ) (ht:0<t):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-2*Fintype.card U*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V:ℝ)))-
      2*Fintype.card V*Real.exp (-2*t^2/J.card)≤
    (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>
      (∀ u,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) u A-(A.card:ℝ)*(1-(∑ g,q u g)-(∑ j,s u j))|<t) ∧
      (∀ v,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v J-∑ u∈J,(1-(∑ g,q u g)-(∑ j,s u j))|<t)) := by
  intro μ f
  let E:=fun σ:RawIntervalFamilyOutcome V U Γ Color=>
      (∀ u,|rawIntervalUnassignedHubCountOn π d σ u A-(A.card:ℝ)*(1-(∑ g,q u g)-(∑ j,s u j))|<t) ∧
      (∀ v,|rawIntervalUnassignedColumnCount π d σ v J-∑ u∈J,(1-(∑ g,q u g)-(∑ j,s u j))|<t)
  have hh:=raw_interval_unassigned_fixed_domains_event π d hd q hq hQ s hs hS hn hnoshort A J t ht
  have heq:(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E (fun e=>z.1 (Sum.inr e)))=
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability E:=by
    calc
      _ = μ.probability (fun ω=>E (fun e=>ω (Sum.inr e))) := finiteLaw_sigma_first_probability μ (fun ω=>ν (f ω)) _
      _ = _ := by
        simpa only [μ,rawExpandedMarkedWheelLaw] using
          (finiteLaw_pi_injective_projection_event
            (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
            Sum.inr Sum.inr_injective E)
  change 1-2*Fintype.card U*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V:ℝ)))-
      2*Fintype.card V*Real.exp (-2*t^2/J.card)≤
    (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E (fun e=>z.1 (Sum.inr e)))
  rw [heq]
  exact hh
end Oberwolfach
