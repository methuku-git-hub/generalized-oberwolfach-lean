module

public import Oberwolfach.MarkedPackingStarDeletionBounds
public import Oberwolfach.MarkedPhysicalDeletionRestriction

@[expose] public section

/-! Full deletion bounds in the active graph follow from the free-root
bounds and the exact avoided inner star of the constructed deep packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem graph_comap_injective_degree_le {V W:Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (D:SimpleGraph V) (f:W↪V) (x:W):(D.comap f).degree x≤D.degree (f x):=by
  rw [graph_comap_degree_into_image,←SimpleGraph.card_neighborFinset_eq_degree]
  exact Finset.card_le_card Finset.inter_subset_left

variable {V U E K V₀ U₀:Type} [Fintype V] [Fintype U] [Fintype V₀] [Fintype U₀]
  [LinearOrder V] [DecidableEq U] [DecidableEq V₀] [DecidableEq U₀]
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {m b:ℕ} {H₀ HK:V→U→Prop}

theorem marked_packing_active_deletion_degrees
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (I T:Finset V) (J W:Finset U)
    (hstar:(M.biUnion markedWheelPhysicalResources).filter (markedStarResource (I\T) (J\W))=∅)
    (f:V₀↪V) (g:U₀↪U) (hf:∀ x,f x∉T) (hg:∀ u,g u∉W)
    (cR cV cU:ℝ) (hcR:0≤cR) (hcV:0≤cV)
    (hR:∀ x∉I,((markedPackingRimGraph M).degree x:ℝ)≤cR)
    (hV:∀ x∉I,((Finset.univ.filter (markedPackingSpokes M x)).card:ℝ)≤cV)
    (hU:∀ u∉W,((Finset.univ.filter (fun x=>markedPackingSpokes M x u)).card:ℝ)≤cU):
    (∀ x,(((markedPackingRimGraph M).comap f).degree x:ℝ)≤cR) ∧
    (∀ x,(((markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)).comap (Sum.map f g)).degree (Sum.inl x):ℝ)≤cV) ∧
    (∀ u,(((markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)).comap (Sum.map f g)).degree (Sum.inr u):ℝ)≤cU):=by
  have hno:=(marked_packing_star_avoidance_neighbours M (I\T) (J\W) hstar).2.2.2.1
  have hs:=markedFiniteSpokeGraph_packing_degrees M
  refine ⟨?_,?_,?_⟩
  · intro x
    have hle:(((markedPackingRimGraph M).comap f).degree x:ℝ)≤(markedPackingRimGraph M).degree (f x):=
      Nat.cast_le.mpr (graph_comap_injective_degree_le _ f x)
    by_cases hx:f x∈I
    · have hz:=marked_packing_star_avoidance_rim_degree_zero M (I\T) (J\W) hstar (f x)
        (Finset.mem_sdiff.mpr ⟨hx,hf x⟩)
      rw [hz,Nat.cast_zero] at hle
      exact hle.trans hcR
    · exact hle.trans (hR (f x) hx)
  · intro x
    have hle:((((markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)).comap (Sum.map f g)).degree (Sum.inl x)):ℝ)≤
        (markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)).degree (Sum.inl (f x)):=
      Nat.cast_le.mpr (graph_comap_injective_degree_le _ (f.sumMap g) (Sum.inl x))
    rw [hs.1] at hle
    by_cases hx:f x∈I
    · have hz:(Finset.univ.filter (markedPackingSpokes M (f x)))=∅:=by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro u hu
        exact hno (f x) (Finset.mem_sdiff.mpr ⟨hx,hf x⟩) u (Finset.mem_filter.mp hu).2
      rw [hz,Finset.card_empty,Nat.cast_zero] at hle
      exact hle.trans hcV
    · exact hle.trans (hV (f x) hx)
  · intro u
    have hle:((((markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)).comap (Sum.map f g)).degree (Sum.inr u)):ℝ)≤
        (markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)).degree (Sum.inr (g u)):=
      Nat.cast_le.mpr (graph_comap_injective_degree_le _ (f.sumMap g) (Sum.inr u))
    rw [hs.2] at hle
    exact hle.trans (hU (g u) (hg u))

end Oberwolfach
