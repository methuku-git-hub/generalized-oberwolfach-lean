module

public import Oberwolfach.MarkedRetainedResourceState
public import Oberwolfach.RawMarkedSpokeDisjointness

@[expose] public section
/-! The approximate packing uses raw colour-two and ordinary spoke states.
Their common typed resource set embeds into physical edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def markedRawSampledPhysicalEmbedding
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color) (g:Γ) (j:Color):
    {z // z∈bernoulliVertexSet (typedMarkedResourceState (rawMarkedPairRims P π d σ)
      (rawMarkedPairSpokes π d σ g j))} ↪ Sym2 V⊕(V×U) where
  toFun z:=typedResourcePhysical π ((markedResourceTypeEquiv (V:=V) (U:=U)) z.val)
  inj' x y h:=by
    apply Subtype.ext
    apply (markedResourceTypeEquiv (V:=V) (U:=U)).injective
    let xx : {z // activeTypedResource P π (3*d) (fun e=>σ (Sum.inl e))
        (rawMarkedPairSpokes π d σ g j) z} :=
      ⟨(markedResourceTypeEquiv (V:=V) (U:=U)) x.val,
        (marked_retained_resource_mem_sample P π d σ _ x.val).mp x.property⟩
    let yy : {z // activeTypedResource P π (3*d) (fun e=>σ (Sum.inl e))
        (rawMarkedPairSpokes π d σ g j) z} :=
      ⟨(markedResourceTypeEquiv (V:=V) (U:=U)) y.val,
        (marked_retained_resource_mem_sample P π d σ _ y.val).mp y.property⟩
    have hd:∀v u,¬(rawMarkedPairSpokes π d σ g j false v u ∧
      rawMarkedPairSpokes π d σ g j true v u) := by
      intro v u
      exact rawMarkedSpokes_disjoint π d (fun e=>σ (Sum.inr e)) g j v u
    have heq:xx=yy:=active_typed_resource_physical_injective P π (3*d) (fun e=>σ (Sum.inl e))
      (rawMarkedPairSpokes π d σ g j) hd h
    exact congrArg (fun z:{z // activeTypedResource P π (3*d) (fun e=>σ (Sum.inl e))
      (rawMarkedPairSpokes π d σ g j) z}=>z.val) heq
end Oberwolfach
