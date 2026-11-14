module

public import Oberwolfach.MarkedSampledPhysicalCandidates
public import Oberwolfach.OrderedOrdinaryWheelExpectation
public import Oberwolfach.BernoulliVertexSampling

@[expose] public section
/-! The Boolean state used in the common sampled-load calculations is
exactly membership in the actual typed retained resource set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_retained_resource_state_eq
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (z:((V×V)⊕(V×V))⊕(Bool×V×U)):
    typedMarkedResourceState (rawMarkedPairRims P π d σ) H z=true ↔
      activeTypedResource P π (3*d) (fun e=>σ (Sum.inl e)) H
        ((markedResourceTypeEquiv (V:=V) (U:=U)) z) := by
  cases z with
  | inl e=>
    cases e with
    | inl xy=>
      rcases xy with ⟨x,y⟩
      simp [typedMarkedResourceState,rawMarkedPairRims,markedResourceTypeEquiv,activeTypedResource]
    | inr xy=>
      rcases xy with ⟨x,y⟩
      simp [typedMarkedResourceState,rawMarkedPairRims,markedResourceTypeEquiv,activeTypedResource]
  | inr x=>
    rcases x with ⟨a,v,u⟩
    simp [typedMarkedResourceState,markedResourceTypeEquiv,activeTypedResource]

theorem marked_retained_resource_mem_sample
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (z:((V×V)⊕(V×V))⊕(Bool×V×U)):
    z∈bernoulliVertexSet (typedMarkedResourceState (rawMarkedPairRims P π d σ) H) ↔
      activeTypedResource P π (3*d) (fun e=>σ (Sum.inl e)) H
        ((markedResourceTypeEquiv (V:=V) (U:=U)) z) := by
  rw [mem_bernoulliVertexSet]
  exact marked_retained_resource_state_eq P π d σ H z
/-- The very ground set used by the sampled matching embeds into physical
edges of the retained marked construction. -/
def markedSampledPhysicalEmbedding
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (g₀:Γ) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g₀) t)
    (g:Γ) (j:Color) :
    {z // z∈bernoulliVertexSet (typedMarkedResourceState (rawMarkedPairRims P π d σ)
      (retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g₀ t J g j))} ↪
      Sym2 V⊕(V×U) where
  toFun z := markedRetainedResourcePhysicalEmbedding P π (3*d) d (fun e=>σ (Sum.inl e))
    (fun e=>σ (Sum.inr e)) g₀ t J g j
      ⟨z.val,(marked_retained_resource_mem_sample P π d σ _ z.val).mp z.property⟩
  inj' x y h := by
    apply Subtype.ext
    have h' := (markedRetainedResourcePhysicalEmbedding P π (3*d) d (fun e=>σ (Sum.inl e))
      (fun e=>σ (Sum.inr e)) g₀ t J g j).injective h
    exact congrArg (fun z : MarkedRetainedResource P π (3*d) d
      (fun e=>σ (Sum.inl e)) (fun e=>σ (Sum.inr e)) g₀ t J g j=>z.val) h' 
end Oberwolfach
