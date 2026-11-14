module

public import Oberwolfach.RawOrdinaryRestrictedCandidatePhysicalLift

@[expose] public section
/-! Every rim arc and spoke of a restricted ordinary wheel belongs to the
same sampled raw state. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_restricted_ordinary_wheel_sampled_resources
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r:ℕ) (raw:RawMarkedOutcome V U Γ Color) (g:Γ) (j:Color):
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=fun W:OrderedOrdinaryWheel (U:=U) π (3*d) r=>(orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding
    ∀W:RestrictedResource R e,
      (∀a:Fin r,rawMarkedPairSpokes π d raw g j false (W.val.1.val a) W.val.2) ∧
      (∀a:Fin r,rawMarkedPairRims P π d raw (Sum.inl (W.val.1.val a,W.val.1.val (cycleNext a)))):=by
  intro state e R W
  have hsample:∀z∈orderedOrdinaryResources W.val,state (ordinaryMarkedResourceEmbedding z)=true:=by
    intro z hz
    have hm:ordinaryMarkedResourceEmbedding z∈R W.val:=Finset.mem_map.mpr ⟨z,hz,rfl⟩
    obtain ⟨x,hx⟩:=W.property _ hm
    have hh:state (e x)=true:=by
      change state x.val=true
      simpa only [bernoulliVertexSet,Finset.mem_filter,Finset.mem_univ,true_and] using x.property
    rw [hx] at hh
    exact hh
  constructor
  · intro a
    have hz:Sum.inr (W.val.1.val a,W.val.2)∈orderedOrdinaryResources W.val:=
      (orderedOrdinaryResources_spoke W.val _).mpr ⟨a,rfl⟩
    have hh:=hsample _ hz
    simpa [state,ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding,
      typedMarkedResourceState] using hh
  · intro a
    have hz:Sum.inl (W.val.1.val a,W.val.1.val (cycleNext a))∈orderedOrdinaryResources W.val:=
      (orderedOrdinaryResources_rim W.val _).mpr ⟨a,rfl⟩
    have hh:=hsample _ hz
    simpa [state,ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding,
      typedMarkedResourceState] using hh
end Oberwolfach
