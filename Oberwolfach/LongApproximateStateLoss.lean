module

public import Oberwolfach.LongMarkedResidualIncomingChange

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]

/-- An old embedding carried by states disjoint from a given state cannot
consume an edge of that state; only the newly embedded loss can. -/
theorem long_approximate_embedding_state_loss
    (G Small Loss:SimpleGraph V)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (j:Fin 6) (T:Finset (Fin 6)) (hT:j∉T)
    (hcover:Small≤longPhysicalStateGraph G ω T⊔Loss):
    ∀x y,sampledColourOrientation G (fun e=>ω (Sum.inl e)) j x y=1→Small.Adj x y→Loss.Adj x y:=by
  intro x y hm hs
  have hc:=hcover hs
  rcases hc with ha|hl
  · have hp:G.Adj x y ∧ (ω (Sum.inl s(x,y)))=(j,orientationBit x y):=by
      by_contra h
      simp [sampledColourOrientation,h] at hm
    have hstate:(ω (Sum.inl s(x,y))).1=j:=congrArg Prod.fst hp.2
    exact False.elim (hT (hstate ▸ ha.2))
  · exact hl
end Oberwolfach
