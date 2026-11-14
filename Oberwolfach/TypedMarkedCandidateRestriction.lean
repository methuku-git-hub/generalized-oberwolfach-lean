module

public import Oberwolfach.OrdinaryMarkedSampledSpokes

@[expose] public section
/-! Restrict an unrestricted marked tuple to its sampled typed rim arcs and
spokes, preserving the tuple and hub exactly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem typed_marked_candidate_restriction
    {V U E L:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype L] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:L→V} {m b:ℕ} {π:Equiv.Perm V}
    (W:MarkedWheel tail head ktail khead m π b (fun _ (_:U)=>True) (fun _ (_:U)=>True))
    (R:E⊕L→Prop) (H:Bool→V→U→Prop)
    (hactive:∀z∈typedMarkedOccurrenceResources W,typedMarkedResourceState R H z=true):
    ∃W':MarkedWheel (fun e:{e:E // R (Sum.inl e)}=>tail e.val) (fun e=>head e.val)
      (fun e:{e:L // R (Sum.inr e)}=>ktail e.val) (fun e=>khead e.val)
      m π b (H false) (H true),W'.1.val=W.1.val ∧ W'.2.val=W.2.val:=by
  have hOrd (i:Fin m):∃e:{e:E // R (Sum.inl e)},tail e.val=W.1.val i.castSucc ∧ head e.val=W.1.val i.succ:=by
    let e:=Classical.choose (W.1.property.2.1 i)
    have he:=Classical.choose_spec (W.1.property.2.1 i)
    have hmem:Sum.inl (Sum.inl e)∈typedMarkedOccurrenceResources W:=by
      apply (typedMarkedOccurrenceResources_rim W (Sum.inl e)).mpr
      exact ⟨i.castSucc,by simp [markedCycleTypedEdge,e]⟩
    have hs:=hactive _ hmem
    have hr:R (Sum.inl e):=by simpa [typedMarkedResourceState] using hs
    exact ⟨⟨e,hr⟩,he⟩
  have hMark:∃e:{e:L // R (Sum.inr e)},ktail e.val=W.1.val (Fin.last m) ∧ khead e.val=W.1.val 0:=by
    let e:=Classical.choose W.1.property.2.2
    have he:=Classical.choose_spec W.1.property.2.2
    have hmem:Sum.inl (Sum.inr e)∈typedMarkedOccurrenceResources W:=by
      apply (typedMarkedOccurrenceResources_rim W (Sum.inr e)).mpr
      exact ⟨Fin.last m,by simp [markedCycleTypedEdge,e]⟩
    have hs:=hactive _ hmem
    have hr:R (Sum.inr e):=by simpa [typedMarkedResourceState] using hs
    exact ⟨⟨e,hr⟩,he⟩
  have hHub:=typed_marked_sampled_spoke_compatibility W R H hactive
  let C':MarkedCycleTuple (fun e:{e:E // R (Sum.inl e)}=>tail e.val) (fun e=>head e.val)
      (fun e:{e:L // R (Sum.inr e)}=>ktail e.val) (fun e=>khead e.val) m π b:=⟨W.1.val,W.1.property.1,hOrd,hMark⟩
  exact ⟨⟨C',⟨W.2.val,hHub⟩⟩,rfl,rfl⟩
end Oberwolfach
