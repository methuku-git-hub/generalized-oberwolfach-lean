module

public import Oberwolfach.MarkedFiniteDeletionDegrees

@[expose] public section

/-! Physical avoidance implies avoidance of the exact original typed
occurrences and spoke pairs used in the reservation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_sample_packing_avoids_reserved_sets
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop):
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E₀=>e.val.1
    let head:=fun e:E₀=>e.val.2
    let ktail:=fun e:E₁=>e.val.1
    let khead:=fun e:E₁=>e.val.2
    ∀ (KA:Finset (E₀⊕E₁)) (KS:Finset (V×U)),
    ∀ M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)),
    Disjoint (markedPackingRimGraph M) (markedSampleArcSetGraph P π d σ KA)→
    (∀ x u,markedPackingSpokes M x u→¬(markedFiniteSpokeGraph KS).Adj (Sum.inl x) (Sum.inr u))→
    M.biUnion markedWheelArcs⊆Finset.univ\KA ∧
    M.biUnion markedWheelSpokePairs⊆
      (Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2))\KS:=by
  intro E₀ E₁ tail head ktail khead KA KS M hR hS
  constructor
  · intro a ha
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
    intro hKA
    have he₁:Sum.elim (fun e=>s(e.val.1,e.val.2)) (fun e=>s(e.val.1,π e.val.2)) a∈
        (markedPackingRimGraph M).edgeFinset:=by
      rw [←markedSampleArcSetGraph_packing P π d m σ H M]
      exact (markedSampleArcSetGraph_coordinate P π d σ _ a).mpr ha
    have he₂:Sum.elim (fun e=>s(e.val.1,e.val.2)) (fun e=>s(e.val.1,π e.val.2)) a∈
        (markedSampleArcSetGraph P π d σ KA).edgeFinset:=
      (markedSampleArcSetGraph_coordinate P π d σ _ a).mpr hKA
    cases a with
    | inl a=>
      exact disjoint_graphs_no_common_edge _ _ hR a.val.1 a.val.2
        (by simpa only [Sum.elim_inl,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using he₁)
        (by simpa only [Sum.elim_inl,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using he₂)
    | inr a=>
      exact disjoint_graphs_no_common_edge _ _ hR a.val.1 (π a.val.2)
        (by simpa only [Sum.elim_inr,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using he₁)
        (by simpa only [Sum.elim_inr,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using he₂)
  · intro z hz
    have hres:Sum.inr z∈M.biUnion markedWheelPhysicalResources:=by
      rw [←markedPackingResources_eq_finite]
      exact (markedFiniteResources_spoke _ _ _ _ π _ _ z).mpr hz
    have hp:markedPackingSpokes M z.1 z.2:=(markedPackingResources_spoke M z.1 z.2).mp hres
    obtain ⟨W,hW,hWu,hWr⟩:=hp
    have hH:=markedWheelPhysicalResources_spoke_present W z.1 z.2
      ((markedWheelPhysicalResources_spoke W z.1 z.2).mpr ⟨hWu,hWr⟩)
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hH⟩,?_⟩
    intro hKS
    exact hS z.1 z.2 ⟨W,hW,hWu,hWr⟩ ((markedFiniteSpokeGraph_adj KS z.1 z.2).mpr hKS)

end Oberwolfach
