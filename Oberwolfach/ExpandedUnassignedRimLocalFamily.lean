module

public import Oberwolfach.ExpandedUnassignedRimLocalScale
public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! Local-scale physical-row tests for a finite family on the same sample. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem raw_expanded_unassigned_rim_local_family_event
    (G:SimpleGraph V) (I:Type) (T:Finset I) (A B:I→Finset V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)]
    (ν:∀ a,FiniteLaw (F a)) (t:I→ℝ) (ht:∀ i∈T,0<t i):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-∑i∈T,2*((B i).card:ℝ)*Real.exp (-2*(t i)^2/((A i).card:ℝ))≤
    (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>∀ i∈T,∀ x∈B i,
      |(((G.neighborFinset x∩A i).filter (fun y=>(z.1 (Sum.inl s(x,y))).1=4)).card:ℝ)-
        u*(G.neighborFinset x∩A i).card|<t i) :=by
  intro μ f
  let E:=fun i (z:Σω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,F (f ω))=>
    ∀x∈B i,|(((G.neighborFinset x∩A i).filter (fun y=>(z.1 (Sum.inl s(x,y))).1=4)).card:ℝ)-
      u*(G.neighborFinset x∩A i).card|<t i
  have hEach:∀i∈T,1-2*((B i).card:ℝ)*Real.exp (-2*(t i)^2/((A i).card:ℝ))≤
      (μ.sigma (fun ω=>ν (f ω))).probability (E i):=by
    intro i hi
    exact raw_expanded_unassigned_rim_degree_local_event G (A i) (B i) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν (t i) (ht i hi)
  exact finiteLaw_high_events_common (μ.sigma (fun ω=>ν (f ω))) T E
    (fun i=>2*((B i).card:ℝ)*Real.exp (-2*(t i)^2/((A i).card:ℝ))) hEach
end Oberwolfach
