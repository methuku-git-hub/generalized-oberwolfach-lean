module

public import Oberwolfach.ExpandedUnassignedRimLocalFamily
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! The local row tests can be intersected with any expanded-law event. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem raw_expanded_unassigned_rim_local_family_with_extra
    (G:SimpleGraph V) (I:Type) (T:Finset I) (A B:I→Finset V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)]
    (ν:∀ a,FiniteLaw (F a)) (t:I→ℝ) (ht:∀ i∈T,0<t i):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    ∀ (Extra:(Σω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,F (f ω))→Prop) (ξ:ℝ),
    1-ξ≤(μ.sigma (fun ω=>ν (f ω))).probability Extra →
    1-ξ-∑i∈T,2*((B i).card:ℝ)*Real.exp (-2*(t i)^2/((A i).card:ℝ))≤
    (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>Extra z ∧ ∀ i∈T,∀ x∈B i,
      |(((G.neighborFinset x∩A i).filter (fun y=>(z.1 (Sum.inl s(x,y))).1=4)).card:ℝ)-
        u*(G.neighborFinset x∩A i).card|<t i)  :=by
  intro μ f Extra ξ hExtra
  let E:=fun z:Σω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,F (f ω)=>
    ∀i∈T,∀x∈B i,|(((G.neighborFinset x∩A i).filter (fun y=>(z.1 (Sum.inl s(x,y))).1=4)).card:ℝ)-
      u*(G.neighborFinset x∩A i).card|<t i
  have hFamily:=raw_expanded_unassigned_rim_local_family_event G I T A B p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν t ht
  exact finiteLaw_intersection_lower (μ.sigma (fun ω=>ν (f ω))) Extra E ξ
    (∑i∈T,2*((B i).card:ℝ)*Real.exp (-2*(t i)^2/((A i).card:ℝ))) hExtra hFamily
end Oberwolfach
