module

public import Oberwolfach.RawMatchingAvoidsSelectedAbsorber
public import Oberwolfach.MarkedFixedTerminalAbsorberOriginal

@[expose] public section
/-! A fixed terminal absorber is contained in the retained selected host,
so the raw approximate resource matching cannot use its physical edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem fixed_absorber_selected_layer_subset
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (g₀:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g₀) t)
    (j₁:Color) (Reserve:Finset (Finset V⊕(V×U))) (X:Finset V) (Z:Finset U):
    let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedMarkedCollapse e (σ e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g₀ t J g₀ j₁
    MarkedFixedTerminalAbsorber P π d m raw H Reserve X Z→
    Reserve⊆(wheelLayerPhysicalResources (longSelectedPhysicalGraph P π d σ) H).image physicalResourceToFinite :=by
  intro raw H habs
  have hsup:Reserve⊆markedFiniteResources
      (fun e:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) false=>e.val.1)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) false=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) true=>e.val.1)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) true=>e.val.2)
      π Finset.univ (Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)):=
    (marked_fixed_terminal_absorber_supported_in_host P π d m raw H Reserve X Z habs).2
  apply selected_absorber_resource_subset
  intro z hz
  have h:=hsup hz
  cases z with
  | inl e=>
    simp only [markedFiniteResources,Finset.mem_union,Finset.mem_image,Sum.inl.injEq,
      Sum.inr_ne_inl,and_false,exists_false,or_false] at h
    obtain ⟨a,_,ha⟩:=h
    cases a with
    | inl a=>
      refine ⟨a.val.1,a.val.2,?_,?_⟩
      · simpa [markedPhysicalEdge] using ha.symm
      · have hh:= (markedSampleArcSetGraph_coordinate P π d raw Finset.univ (Sum.inl a)).mpr (Finset.mem_univ _)
        exact SimpleGraph.mem_edgeFinset.mp (by simpa only [longSelectedPhysicalGraph,Sum.elim_inl] using hh)
    | inr a=>
      refine ⟨a.val.1,π a.val.2,?_,?_⟩
      · simpa [markedPhysicalEdge] using ha.symm
      · have hh:= (markedSampleArcSetGraph_coordinate P π d raw Finset.univ (Sum.inr a)).mpr (Finset.mem_univ _)
        exact SimpleGraph.mem_edgeFinset.mp (by simpa only [longSelectedPhysicalGraph,Sum.elim_inr] using hh)
  | inr vu=>
    have hS:vu∈Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2):=
      (markedFiniteResources_spoke _ _ _ _ _ _ _ _).mp h
    rcases (Finset.mem_filter.mp hS).2 with hf|ht
    · exact ⟨false,hf⟩
    · exact ⟨true,ht⟩
/-- The preselected fixed absorber survives every approximate matching,
without deleting its edges from the approximate sampling law. -/
theorem raw_matching_avoids_fixed_terminal_absorber
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (g₀ g₂:Γ) (hg:g₂≠g₀) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g₀) t)
    (j₁ j₂:Color) (hj:j₂≠j₁) (Reserve:Finset (Finset V⊕(V×U))) (X:Finset V) (Z:Finset U):
    let selected:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedMarkedCollapse e (σ e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g₀ t J g₀ j₁
    let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let W:Type:={z // z∈bernoulliVertexSet (typedMarkedResourceState (rawMarkedPairRims P π d raw)
      (rawMarkedPairSpokes π d raw g₂ j₂))}
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g₂ j₂
    MarkedFixedTerminalAbsorber P π d m selected H Reserve X Z→
    ∀(C:Type) [Fintype C] [DecidableEq C] (Q:C→Finset W) (M:Finset C),
    Disjoint ((M.biUnion Q).image (fun w=>physicalResourceToFinite (φ w))) Reserve :=by
  intro selected H raw W φ habs C _ _ Q M
  have h:=fixed_absorber_selected_layer_subset P π d m σ g₀ t J j₁ Reserve X Z habs
  exact raw_matching_avoids_selected_absorber P π d σ g₀ g₂ hg t J j₁ j₂ hj C Q M Reserve h
end Oberwolfach
