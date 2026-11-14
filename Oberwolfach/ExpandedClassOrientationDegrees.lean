module

public import Oberwolfach.LongPreparationPhysicalStates
public import Oberwolfach.MarkedExpandedDegreeEvent

@[expose] public section
/-! The sampled class consists exactly of physical states zero through four,
and its stored orientation is the sum of their directed indicators. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_class_orientation_degrees
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P:SimpleGraph V) (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) (v:V):
    (∑w,sampledOrientation (longPhysicalStateGraph P σ {0,1,2,3,4}) (fun e=>(σ (Sum.inl e)).2) v w)=
      ∑a∈({0,1,2,3,4}:Finset (Fin 6)),∑w,sampledColourOrientation P (fun e=>σ (Sum.inl e)) a v w:=by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hp:P.Adj v w
  · have hs:∃a:Fin 6,∃b:Bool,σ (Sum.inl s(v,w))=(a,b):=by
      exact ⟨(σ (Sum.inl s(v,w))).1,(σ (Sum.inl s(v,w))).2,by cases σ (Sum.inl s(v,w));rfl⟩
    obtain ⟨a,b,hab⟩:=hs
    fin_cases a <;> cases b <;> cases hbit:orientationBit v w <;>
      simp [sampledOrientation,longPhysicalStateGraph,sampledColourOrientation,hp,hab,hbit]
  · simp [sampledOrientation,longPhysicalStateGraph,sampledColourOrientation,hp]
end Oberwolfach
