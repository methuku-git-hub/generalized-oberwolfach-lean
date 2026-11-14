module

public import Oberwolfach.RawUnassignedHubLocalEvent
public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! One interval sample satisfies all prescribed local unassigned-spoke rows. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_interval_unassigned_hub_local_family_event
    {V U Γ Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color]
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (I:Type) (T:Finset I) (A:I→Finset V) (B:I→Finset U) (t:I→ℝ)
    (hA:∀i∈T,0<(A i).card) (ht:∀i∈T,0<t i):
    let μ:=FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
    1-∑i∈T,2*((B i).card:ℝ)*Real.exp (-2*(t i)^2/((4*(d:ℝ)+3)^2*((A i).card:ℝ)))≤
      μ.probability (fun σ=>∀i∈T,∀u∈B i,|rawIntervalUnassignedHubCountOn π d σ u (A i)-
        ((A i).card:ℝ)*(1-(∑g,q u g)-(∑j,s u j))|<t i):=by
  intro μ
  let E:=fun i (σ:RawIntervalFamilyOutcome V U Γ Color)=>∀u∈B i,|rawIntervalUnassignedHubCountOn π d σ u (A i)-
    ((A i).card:ℝ)*(1-(∑g,q u g)-(∑j,s u j))|<t i
  have hEach:∀i∈T,1-2*((B i).card:ℝ)*Real.exp (-2*(t i)^2/((4*(d:ℝ)+3)^2*((A i).card:ℝ)))≤μ.probability (E i):=by
    intro i hi
    exact raw_interval_unassigned_hub_local_event π d hd q hq hQ s hs hS hnoshort (A i) (B i) (hA i hi) (t i) (ht i hi)
  exact finiteLaw_high_events_common μ T E
    (fun i=>2*((B i).card:ℝ)*Real.exp (-2*(t i)^2/((4*(d:ℝ)+3)^2*((A i).card:ℝ)))) hEach
end Oberwolfach
