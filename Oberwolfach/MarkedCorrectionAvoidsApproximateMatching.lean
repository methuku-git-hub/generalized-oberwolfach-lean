module

public import Oberwolfach.RawMatchingAvoidsSelectedAbsorber
public import Oberwolfach.MarkedFinitePhysicalDeletion
public import Oberwolfach.MarkedFiniteResourceOperations

@[expose] public section
/-! Finite marked corrections use selected physical resources and are disjoint
from every matching on the approximate layer of the same expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem marked_correction_resources_in_selected_layer
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (g₀:Γ) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g₀) t)
    (j:Color):
    let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedMarkedCollapse e (σ e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g₀ t J g₀ j
    let E:=MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) true;
    ∀ (A:Finset (E⊕K)) (S:Finset (V×U)),
      S⊆Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2) →
      markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π A S ⊆
        (wheelLayerPhysicalResources (longSelectedPhysicalGraph P π d σ) H).image physicalResourceToFinite := by
  intro raw H E K A S hS
  apply selected_absorber_resource_subset (longSelectedPhysicalGraph P π d σ) H
  intro z hz
  simp only [markedFiniteResources,Finset.mem_union,Finset.mem_image] at hz
  rcases hz with ⟨a,ha,rfl⟩|⟨⟨x,u⟩,hs,rfl⟩
  · cases a with
    | inl e=>
      refine ⟨e.val.1,e.val.2,rfl,?_⟩
      change (markedSampleArcSetGraph P π d raw Finset.univ).Adj e.val.1 e.val.2
      have hh: s(e.val.1,e.val.2)∈(markedSampleArcSetGraph P π d raw Finset.univ).edgeFinset:=by
        simpa only [Sum.elim_inl] using
          (markedSampleArcSetGraph_coordinate P π d raw Finset.univ (Sum.inl e)).mpr (Finset.mem_univ _)
      exact SimpleGraph.mem_edgeFinset.mp hh
    | inr e=>
      refine ⟨e.val.1,π e.val.2,rfl,?_⟩
      change (markedSampleArcSetGraph P π d raw Finset.univ).Adj e.val.1 (π e.val.2)
      have hh: s(e.val.1,π e.val.2)∈(markedSampleArcSetGraph P π d raw Finset.univ).edgeFinset:=by
        simpa only [Sum.elim_inr] using
          (markedSampleArcSetGraph_coordinate P π d raw Finset.univ (Sum.inr e)).mpr (Finset.mem_univ _)
      exact SimpleGraph.mem_edgeFinset.mp hh
  · rcases (Finset.mem_filter.mp (hS hs)).2 with h|h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩

theorem marked_correction_disjoint_from_approximate_matching
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (g₀ g₂:Γ) (hg:g₂≠g₀) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g₀) t)
    (j₁ j₂:Color) (hj:j₂≠j₁):
    let selected:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedMarkedCollapse e (σ e)
    let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g₀ t J g₀ j₁
    let E:=MarkedSampleArc P π (3*d) (fun e=>selected (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>selected (Sum.inl e)) true
    let W:Type:={z // z∈bernoulliVertexSet (typedMarkedResourceState (rawMarkedPairRims P π d raw)
      (rawMarkedPairSpokes π d raw g₂ j₂))}
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g₂ j₂;
    ∀(C:Type) [Fintype C] [DecidableEq C] (Q:C→Finset W) (M:Finset C)
      (A:Finset (E⊕K)) (S:Finset (V×U)),
      S⊆Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2) →
      Disjoint ((M.biUnion Q).image (fun w=>physicalResourceToFinite (φ w)))
        (markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
          (fun e:K=>e.val.1) (fun e=>e.val.2) π A S) := by
  intro selected raw H E K W φ C _ _ Q M A S hS
  exact raw_matching_avoids_selected_absorber P π d σ g₀ g₂ hg t J j₁ j₂ hj C Q M _
    (marked_correction_resources_in_selected_layer P π d σ g₀ t J j₁ A S hS)
theorem marked_correction_rims_avoid_approximate_graph
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e):
    let selected:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedMarkedCollapse e (σ e)
    let E:=MarkedSampleArc P π (3*d) (fun e=>selected (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>selected (Sum.inl e)) true;
    ∀ (A:Finset (E⊕K)), Disjoint (markedSampleArcSetGraph P π d selected A)
      (longApproximatePhysicalGraph P π d σ) := by
  intro selected E K A
  have hsub:markedSampleArcSetGraph P π d selected A ≤ longSelectedPhysicalGraph P π d σ := by
    intro x y hxy
    change (markedSampleArcSetGraph P π d selected Finset.univ).Adj x y
    exact ⟨hxy.1,(Finset.image_mono _ (Finset.subset_univ A)) hxy.2⟩
  exact (selected_and_approximate_rim_graphs_disjoint P π d σ).mono_left hsub
end Oberwolfach
