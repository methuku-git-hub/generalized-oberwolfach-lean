module

public import Oberwolfach.LongApproximatePhysicalStates
public import Oberwolfach.MarkedRawSampledPhysicalEmbedding

@[expose] public section
/-! Every eligible approximate rim edge has its actual raw typed resource
in the sampled physical embedding, with the original orientation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem long_approximate_edge_has_raw_resource
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (g:Γ) (j:Color) (x y:V)
    (h:(longApproximatePhysicalGraph P π d σ).Adj x y):
    let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedApproximateCollapse e (σ e)
    ∃w,markedRawSampledPhysicalEmbedding P π d raw g j w=Sum.inl s(x,y) := by
  intro raw
  change x≠y ∧ ({x,y}:Finset V)∈
    (Finset.univ.image (markedPhysicalEdge
      (fun e:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) false=>e.val.1)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) false=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) true=>e.val.1)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) true=>e.val.2) π)) at h
  obtain ⟨a,_,ha⟩:=Finset.mem_image.mp h.2
  have hpair {a b c e:V} (hh:({a,b}:Finset V)={c,e}):s(a,b)=s(c,e):=by
    apply Sym2.eq_iff.mpr
    apply Set.pair_eq_pair_iff.mp
    simpa only [Finset.coe_pair] using congrArg (fun S:Finset V=>(S:Set V)) hh
  cases a with
  | inl e=>
    let root:((V×V)⊕(V×V))⊕(Bool×V×U):=Sum.inl (Sum.inl e.val)
    have hs:typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j) root=true := by
      simpa [root,typedMarkedResourceState,rawMarkedPairRims] using e.property
    let w : {z // z∈bernoulliVertexSet (typedMarkedResourceState (rawMarkedPairRims P π d raw)
      (rawMarkedPairSpokes π d raw g j))} := ⟨root,(mem_bernoulliVertexSet _ _).mpr hs⟩
    refine ⟨w,?_⟩
    have hp:s(e.val.1,e.val.2)=s(x,y):=hpair (by simpa [markedPhysicalEdge] using ha)
    simpa [w,root,markedRawSampledPhysicalEmbedding,typedResourcePhysical,markedResourceTypeEquiv] using congrArg (fun z:Sym2 V=>(Sum.inl z:Sym2 V⊕(V×U))) hp
  | inr e=>
    let root:((V×V)⊕(V×V))⊕(Bool×V×U):=Sum.inl (Sum.inr e.val)
    have hs:typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j) root=true := by
      simpa [root,typedMarkedResourceState,rawMarkedPairRims] using e.property
    let w : {z // z∈bernoulliVertexSet (typedMarkedResourceState (rawMarkedPairRims P π d raw)
      (rawMarkedPairSpokes π d raw g j))} := ⟨root,(mem_bernoulliVertexSet _ _).mpr hs⟩
    refine ⟨w,?_⟩
    have hp:s(e.val.1,π e.val.2)=s(x,y):=hpair (by simpa [markedPhysicalEdge] using ha)
    simpa [w,root,markedRawSampledPhysicalEmbedding,typedResourcePhysical,markedResourceTypeEquiv] using congrArg (fun z:Sym2 V=>(Sum.inl z:Sym2 V⊕(V×U))) hp
end Oberwolfach
