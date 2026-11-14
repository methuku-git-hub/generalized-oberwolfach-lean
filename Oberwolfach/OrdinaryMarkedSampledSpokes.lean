module

public import Oberwolfach.OrdinaryPhysicalMarkedPayload
public import Oberwolfach.TypedMarkedLoadBounds

@[expose] public section
/-! A sampled marked candidate really has its marked and ordinary spokes
in the sample; the initially unrestricted hub witness can be refined. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem typed_marked_sampled_spoke_compatibility
    {V U E L:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype L] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:L→V} {m b:ℕ} {π:Equiv.Perm V}
    (W:MarkedWheel tail head ktail khead m π b (fun _ (_:U)=>True) (fun _ (_:U)=>True))
    (R:E⊕L→Prop) (H:Bool→V→U→Prop)
    (hsampled:∀a∈typedMarkedOccurrenceResources W,typedMarkedResourceState R H a=true):
    MarkedHubCompatible (H false) (H true) W.1.val W.2.val :=by
  constructor
  · have hmem:Sum.inr (true,W.1.val 0,W.2.val)∈typedMarkedOccurrenceResources W:=by
      apply (typedMarkedOccurrenceResources_spoke W _).2
      exact ⟨0,by simp⟩
    have hh:=hsampled _ hmem
    simpa only [typedMarkedResourceState,Sum.elim_inr,decide_eq_true_eq] using hh
  · intro i
    have hmem:Sum.inr (false,W.1.val i.succ,W.2.val)∈typedMarkedOccurrenceResources W:=by
      apply (typedMarkedOccurrenceResources_spoke W _).2
      exact ⟨i.succ,by simp⟩
    have hh:=hsampled _ hmem
    simpa only [typedMarkedResourceState,Sum.elim_inr,decide_eq_true_eq] using hh
end Oberwolfach
