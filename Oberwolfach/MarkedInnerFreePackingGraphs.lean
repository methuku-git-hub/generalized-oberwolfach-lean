module

public import Oberwolfach.MarkedInnerDeletionBudgets

@[expose] public section
/-! A packing with no physical resource inside the inner pair has no
physical rim edge or spoke inside that pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {m b:ℕ} {H₀ HK:V→U→Prop}

theorem marked_inner_free_packing_graphs
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK)) (I:Finset V) (J:Finset U)
    (hinner:(M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=∅):
    (∀ x∈I,∀ y∈I,¬(markedPackingRimGraph M).Adj x y) ∧
    (∀ x∈I,∀ u∈J,¬(markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)).Adj (Sum.inl x) (Sum.inr u)) :=by
  have hno (e:Finset V⊕(V×U)) (he:e∈M.biUnion markedWheelPhysicalResources)
      (hi:markedInnerResource I J e):False:=by
    have hh:e∈(M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J):=
      Finset.mem_filter.mpr ⟨he,hi⟩
    rw [hinner] at hh
    exact Finset.notMem_empty e hh
  constructor
  · intro x hx y hy hadj
    have hed:{x,y}∈markedPackingRims M:=by
      have hh:=hadj
      simp only [markedPackingRimGraph,physicalEdgeGraph] at hh
      exact hh.2
    obtain ⟨C,hC,he⟩:=Finset.mem_biUnion.mp hed
    have hres:Sum.inl ({x,y}:Finset V)∈M.biUnion markedWheelPhysicalResources:=
      Finset.mem_biUnion.mpr ⟨C,hC,(markedWheelPhysicalResources_rim C _).mpr he⟩
    have hi:markedInnerResource I J (Sum.inl ({x,y}:Finset V)):=by
      change ({x,y}:Finset V)⊆I
      intro z hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl|rfl <;> assumption
    exact hno _ hres hi
  · intro x hx u hu hadj
    obtain ⟨C,hC,hCu,hCx⟩:=(markedFiniteSpokeGraph_packing_adj M x u).mp hadj
    have hres:Sum.inr (x,u)∈M.biUnion markedWheelPhysicalResources:=
      Finset.mem_biUnion.mpr ⟨C,hC,(markedWheelPhysicalResources_spoke C x u).mpr
        ⟨hCu,by simpa only [markedWheelRows] using hCx⟩⟩
    have hi:markedInnerResource I J (Sum.inr (x,u)):=⟨hx,hu⟩
    exact hno _ hres hi
end Oberwolfach
