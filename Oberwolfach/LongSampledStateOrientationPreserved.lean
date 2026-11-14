module

public import Oberwolfach.LongEveryClassSameDeletionReady
public import Oberwolfach.RandomColourCuts

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]

/-- A sampled direction in the class reference survives outside the physical correction deletion. -/
theorem long_sampled_state_direction_preserved
    (P Del:SimpleGraph V) (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (M:V→V→ℕ) (j:Fin 6) (hj:j∈({0,1,2,3,4}:Finset (Fin 6)))
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph P ω {0,1,2,3,4})
      (fun e=>(ω (Sum.inl e)).2) M≤Del):
    ∀x y,sampledColourOrientation P (fun e=>ω (Sum.inl e)) j x y=1→¬Del.Adj x y→M x y=1 :=by
  intro x y hsel hDel
  have hh:P.Adj x y ∧ ω (Sum.inl s(x,y))=(j,orientationBit x y):=by
    by_contra h
    simp [sampledColourOrientation,h] at hsel
  have hstate:(longPhysicalStateGraph P ω {0,1,2,3,4}).Adj x y:=by
    refine ⟨hh.1,?_⟩
    rw [hh.2]
    exact hj
  have hsample:sampledOrientation (longPhysicalStateGraph P ω {0,1,2,3,4})
      (fun e=>(ω (Sum.inl e)).2) x y=1:=by
    simp [sampledOrientation,hstate,hh.2]
  by_contra hn
  apply hDel
  apply hcorrect
  exact ⟨hstate,Or.inl (by simpa [hsample] using hn)⟩
end Oberwolfach
