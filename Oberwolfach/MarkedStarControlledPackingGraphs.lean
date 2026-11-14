module

public import Oberwolfach.MarkedInnerFreePackingGraphs
public import Oberwolfach.MarkedInnerStarAvoidsActive

@[expose] public section
/-! A packing whose inner resources lie in the removed star avoids the
remaining inner pair, as physical rim and spoke graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {m b:ℕ} {H₀ HK:V→U→Prop}

theorem marked_star_controlled_packing_graphs
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (I T:Finset V) (J W:Finset U) (A:Finset (Finset V⊕(V×U)))
    (hfilter:(M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=
      A.filter (markedStarResource T W)):
    (∀ x∈I\T,∀ y∈I\T,¬(markedPackingRimGraph M).Adj x y) ∧
    (∀ x∈I\T,∀ u∈J\W,¬(markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)).Adj (Sum.inl x) (Sum.inr u)) :=by
  have hstar:∀ e∈M.biUnion markedWheelPhysicalResources,
      markedInnerResource I J e→markedStarResource T W e:=by
    intro e he hi
    have hh:e∈(M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J):=
      Finset.mem_filter.mpr ⟨he,hi⟩
    rw [hfilter] at hh
    exact (Finset.mem_filter.mp hh).2
  have hinner:=marked_inner_star_avoids_active (M.biUnion markedWheelPhysicalResources) I T J W hstar
  exact marked_inner_free_packing_graphs M (I\T) (J\W) hinner
end Oberwolfach
