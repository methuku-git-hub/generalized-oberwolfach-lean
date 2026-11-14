module

public import Oberwolfach.RawUnassignedHubLocalScale
public import Oberwolfach.CommonEvents

@[expose] public section
/-! Local unassigned-spoke rows for a prescribed set of hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_interval_unassigned_hub_local_event
    {V U Γ Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color]
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (A:Finset V) (B:Finset U) (hA:0<A.card) (t:ℝ) (ht:0<t):
    let μ:=FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
    1-2*(B.card:ℝ)*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(A.card:ℝ)))≤
      μ.probability (fun σ=>∀u∈B,|rawIntervalUnassignedHubCountOn π d σ u A-
        (A.card:ℝ)*(1-(∑g,q u g)-(∑j,s u j))|<t):=by
  intro μ
  have hh:=finiteLaw_common_event_lower μ B
    (fun u σ=>t≤|rawIntervalUnassignedHubCountOn π d σ u A-
      (A.card:ℝ)*(1-(∑g,q u g)-(∑j,s u j))|)
    (fun _=>2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(A.card:ℝ))))
    (fun u _=>by
      have ht':=rawIntervalUnassignedHubCountOn_local_tail π d hd q hq hQ s hs hS u A hA t ht
      rw [rawIntervalUnassignedHubCountOn_expectation π d hd q hq hQ s hs hS hnoshort u A] at ht'
      exact ht')
  simp only [Finset.sum_const,nsmul_eq_mul,not_le] at hh
  convert hh using 1 <;> ring
end Oberwolfach
