module

public import Oberwolfach.ExpandedDensityOneSupport
public import Oberwolfach.LongPreparationPhysicalContainment

@[expose] public section
/-! With no state-five physical coordinates, the sampled class is the
ambient graph. Thus a regular ambient graph needs no regularisation or edits. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_class_eq_host_of_no_state_five
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P:SimpleGraph V) (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (hfive:∀e:Sym2 V,(σ (Sum.inl e)).1≠5):
    longPhysicalStateGraph P σ {0,1,2,3,4}=P:=by
  ext x y
  simp only [longPhysicalStateGraph]
  constructor
  · intro h;exact h.1
  · intro h
    refine ⟨h,?_⟩
    have hf:=hfive s(x,y)
    generalize hz:(σ (Sum.inl s(x,y))).1=a at *
    fin_cases a <;> simp_all
end Oberwolfach
