module

public import Oberwolfach.ExpandedBinaryClassLaw
public import Oberwolfach.LongPreparationPhysicalStates
public import Oberwolfach.ColourRestriction

@[expose] public section
/-! Binary colour zero is precisely the sampled class graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_binary_class_graph
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P:SimpleGraph V) (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e):
    edgeColourGraph P (fun e=>(expandedBinaryClass (σ (Sum.inl e))).1) 0=
      longPhysicalStateGraph P σ {0,1,2,3,4}:=by
  ext x y
  change P.Adj x y ∧ (expandedBinaryClass (σ (Sum.inl s(x,y)))).1=0 ↔
    P.Adj x y ∧ (σ (Sum.inl s(x,y))).1∈({0,1,2,3,4}:Finset (Fin 6))
  rcases σ (Sum.inl s(x,y)) with ⟨a,b⟩
  fin_cases a <;> simp [expandedBinaryClass]
end Oberwolfach
