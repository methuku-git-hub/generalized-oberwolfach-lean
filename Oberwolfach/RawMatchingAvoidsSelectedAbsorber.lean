module

public import Oberwolfach.RawApproximateEmbeddingLayer

@[expose] public section
/-! The physical resources of any matching on the raw approximate ground
set avoid an absorber contained in the retained selected layer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

def physicalResourceToFinite:Sym2 V⊕(V×U)→Finset V⊕(V×U):=
  Sum.map Sym2.toFinset id

theorem physical_resource_to_finite_injective:
    Function.Injective (physicalResourceToFinite (V:=V) (U:=U)):=by
  intro a b h
  cases a with
  | inl a=>
    cases b with
    | inl b=>
      apply congrArg Sum.inl
      induction a using Sym2.ind with
      | _ x y=>
        induction b using Sym2.ind with
        | _ z w=>
          have hp:({x,y}:Finset V)={z,w}:=by simpa [physicalResourceToFinite,Sym2.toFinset_mk_eq] using h
          apply Sym2.eq_iff.mpr
          apply Set.pair_eq_pair_iff.mp
          simpa only [Finset.coe_pair] using congrArg (fun S:Finset V=>(S:Set V)) hp
    | inr b=>cases h
  | inr a=>
    cases b with
    | inl b=>cases h
    | inr b=>
      apply congrArg Sum.inr
      exact Sum.inr.inj h

theorem raw_matching_avoids_selected_absorber
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (g₀ g₂:Γ) (hg:g₂≠g₀) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g₀) t)
    (j₁ j₂:Color) (hj:j₂≠j₁):
    let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let W:Type:={z // z∈bernoulliVertexSet (typedMarkedResourceState (rawMarkedPairRims P π d raw)
      (rawMarkedPairSpokes π d raw g₂ j₂))}
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g₂ j₂
    ∀(C:Type) [Fintype C] [DecidableEq C] (Q:C→Finset W) (M:Finset C)
      (Absorber:Finset (Finset V⊕(V×U))),
    Absorber⊆(wheelLayerPhysicalResources (longSelectedPhysicalGraph P π d σ)
      (retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g₀ t J g₀ j₁)).image physicalResourceToFinite →
    Disjoint ((M.biUnion Q).image (fun w=>physicalResourceToFinite (φ w))) Absorber :=by
  intro raw W φ C _ _ Q M Absorber hAbs
  have hsub:(M.biUnion Q).image φ⊆wheelLayerPhysicalResources (longApproximatePhysicalGraph P π d σ)
      (rawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g₂ j₂):=by
    intro z hz
    obtain ⟨w,_,rfl⟩:=Finset.mem_image.mp hz
    exact raw_sampled_physical_embedding_in_approximate_layer P π d σ g₂ j₂ w
  have hd:=raw_approximate_and_retained_selected_physical_disjoint P π d σ g₀ g₂ hg t J j₁ j₂ hj
  apply Finset.disjoint_left.mpr
  intro x hx hxa
  obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hx
  obtain ⟨z,hz,hzeq⟩:=Finset.mem_image.mp (hAbs hxa)
  have hzw:z=φ w:=physical_resource_to_finite_injective hzeq
  subst z
  have hw':φ w∈wheelLayerPhysicalResources (longApproximatePhysicalGraph P π d σ)
      (rawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g₂ j₂):=hsub (Finset.mem_image.mpr ⟨w,hw,rfl⟩)
  exact Finset.disjoint_left.mp hd hw' hz
/-- An absorber whose physical rim edges and spokes lie in the selected
host is automatically contained in the selected layer representation. -/
theorem selected_absorber_resource_subset
    (G:SimpleGraph V) (H:Bool→V→U→Prop) (Absorber:Finset (Finset V⊕(V×U)))
    (hA:∀z∈Absorber,match z with
      | Sum.inl e=>∃x y,e={x,y} ∧ G.Adj x y
      | Sum.inr (v,u)=>∃b,H b v u):
    Absorber⊆(wheelLayerPhysicalResources G H).image physicalResourceToFinite :=by
  intro z hz
  specialize hA z hz
  cases z with
  | inl e=>
    obtain ⟨x,y,rfl,hxy⟩:=hA
    apply Finset.mem_image.mpr
    refine ⟨Sum.inl s(x,y),?_,?_⟩
    · simp only [wheelLayerPhysicalResources,Finset.mem_union,Finset.mem_image]
      left
      exact ⟨s(x,y),SimpleGraph.mem_edgeFinset.mpr hxy,rfl⟩
    · simp [physicalResourceToFinite,Sym2.toFinset_mk_eq]
  | inr vu=>
    rcases vu with ⟨v,u⟩
    obtain ⟨b,hb⟩:=hA
    apply Finset.mem_image.mpr
    refine ⟨Sum.inr (v,u),?_,rfl⟩
    simp only [wheelLayerPhysicalResources,Finset.mem_union,Finset.mem_image]
    right
    exact ⟨(v,u),Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨b,hb⟩⟩,rfl⟩
end Oberwolfach
