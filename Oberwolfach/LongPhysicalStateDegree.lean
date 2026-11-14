module

public import Oberwolfach.LongPreparationPhysicalStates
public import Oberwolfach.ColourDegrees

@[expose] public section
/-! A single physical exposure state's degree is the sampled colour degree. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_physical_state_singleton_degree
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P:SimpleGraph V) (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (c:Fin 6) (x:V):
    (longPhysicalStateGraph P σ {c}).degree x=
      sampledColourDegree P (fun e=>(σ (Sum.inl e)).1) c x:=by
  rw [←SimpleGraph.card_neighborFinset_eq_degree]
  unfold sampledColourDegree
  congr 1
  ext y
  simp only [SimpleGraph.mem_neighborFinset,Finset.mem_filter]
  change (P.Adj x y ∧ (σ (Sum.inl s(x,y))).1∈({c}:Finset (Fin 6))) ↔ (P.Adj x y ∧ (σ (Sum.inl s(x,y))).1=c)
  simp
end Oberwolfach
