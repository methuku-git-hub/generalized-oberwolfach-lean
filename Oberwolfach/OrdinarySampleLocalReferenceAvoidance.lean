module

public import Oberwolfach.OrdinarySampleForcedSpokes

@[expose] public section
/-! The selected reserved-label list is exactly the reference spoke layer,
so local list avoidance gives the local spoke avoidance needed by the trace. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_sample_local_reference_avoidance
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {X:U→Type} (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e)
    (Inner:Finset V) (Hubs:Finset U) (f:∀u,X u→V)
    (h:∀u,u∈Hubs→∀x,f u x∈Inner→f u x∉rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u):
    ∀u,u∈Hubs→∀x,f u x∈Inner→
      ¬rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false (f u x) u :=by
  intro u hu x hx href
  apply h u hu x hx
  have hh:rawIntervalFamilyState π d (fun e=>σ (Sum.inr e)) (f u x,u)=some (Sum.inr false):=
    (ordinary_reference_spoke_projection π d σ false (f u x) u).mp href
  simpa only [rawReservedSpokeList,rawIntervalOrdinaryOuter,Finset.mem_filter,Finset.mem_univ,true_and] using hh
end Oberwolfach
