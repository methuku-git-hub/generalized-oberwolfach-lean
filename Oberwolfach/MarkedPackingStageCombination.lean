module

public import Oberwolfach.MarkedRowCoverPackings

@[expose] public section

/-! Combine hub and row stages using their actual physical rim graphs and
hub sets. Distinct auxiliary representations are never used to justify
physical edge disjointness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head : E→V} {ktail khead : T→V} {H₀ HK : V→U→Prop}
    {π : Equiv.Perm V} {m b n K : ℕ}

theorem marked_packings_disjoint_of_rims_and_hubs (hm : 1≤m) (hb : 1≤b)
    (M N : Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hrim : Disjoint (markedPackingRimGraph M) (markedPackingRimGraph N))
    (hhubs : ∀ W∈M,∀ Z∈N,W.2.val≠Z.2.val) :
    Disjoint (M.biUnion markedWheelPhysicalResources) (N.biUnion markedWheelPhysicalResources) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨W,hW,he⟩ := Finset.mem_biUnion.mp he
  obtain ⟨Z,hZ,hf⟩ := Finset.mem_biUnion.mp hf
  cases e with
  | inr p=>
    exact hhubs W hW Z hZ (((markedWheelPhysicalResources_spoke W p.1 p.2).mp he).1.trans
      ((markedWheelPhysicalResources_spoke Z p.1 p.2).mp hf).1.symm)
  | inl e=>
    have he' := (markedWheelPhysicalResources_rim W e).mp he
    have hf' := (markedWheelPhysicalResources_rim Z e).mp hf
    have hcard : e.card=2 := by
      obtain ⟨a,_,ha⟩ := Finset.mem_image.mp he'
      rw [←ha]
      exact markedCycle_physical_edge_card tail head ktail khead m π b hm hb W.1 a
    obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp hcard
    exact disjoint_graphs_no_common_edge _ _ hrim x y
      ⟨hxy,Finset.mem_biUnion.mpr ⟨W,hW,he'⟩⟩ ⟨hxy,Finset.mem_biUnion.mpr ⟨Z,hZ,hf'⟩⟩

theorem marked_hub_row_stages_combine (hm : 1≤m) (hb : 1≤b)
    (M : Finset (MarkedWheel tail head ktail khead m π b H₀ HK)) (Z : Finset U)
    (hM : ∀ W∈M,∀ X∈M,W≠X→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources X))
    (hMhub : ∀ W∈M,W.2.val∈Z)
    (C : Fin n→Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (v : Fin n→V) (F : Finset V) (required : Fin n→Finset (Finset V⊕(V×U))) (Y : Fin n→Finset U)
    (hC : ∀ i,MarkedRowCover (C i) (v i) F (required i) (Y i) K)
    (hcross : ∀ i j,i≠j→Disjoint ((C i).biUnion markedWheelPhysicalResources) ((C j).biUnion markedWheelPhysicalResources))
    (hR : ∀ i,Disjoint (markedPackingRimGraph (C i)) (markedPackingRimGraph M))
    (hY : ∀ i,Disjoint (Y i) Z) :
    let N := M∪Finset.univ.biUnion C
    (∀ W∈N,∀ X∈N,W≠X→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources X)) ∧
    M.biUnion markedWheelPhysicalResources ∪ Finset.univ.biUnion required⊆N.biUnion markedWheelPhysicalResources := by
  let N := M∪Finset.univ.biUnion C
  have hMC (i) : Disjoint ((C i).biUnion markedWheelPhysicalResources) (M.biUnion markedWheelPhysicalResources) :=
    marked_packings_disjoint_of_rims_and_hubs hm hb (C i) M (hR i)
      (fun W hW X hX he=>Finset.disjoint_left.mp (hY i) ((hC i).hubs W hW) (he ▸ hMhub X hX))
  refine ⟨?_,?_⟩
  · intro W hW X hX hne
    rcases Finset.mem_union.mp hW with hW|hW <;> rcases Finset.mem_union.mp hX with hX|hX
    · exact hM W hW X hX hne
    · obtain ⟨j,_,hX⟩ := Finset.mem_biUnion.mp hX
      exact (hMC j).symm.mono (resource_subset_union _ M W hW) (resource_subset_union _ (C j) X hX)
    · obtain ⟨i,_,hW⟩ := Finset.mem_biUnion.mp hW
      exact (hMC i).mono (resource_subset_union _ (C i) W hW) (resource_subset_union _ M X hX)
    · obtain ⟨i,_,hW⟩ := Finset.mem_biUnion.mp hW
      obtain ⟨j,_,hX⟩ := Finset.mem_biUnion.mp hX
      by_cases hij : i=j
      · subst j
        exact (hC i).disjoint W hW X hX hne
      · exact (hcross i j hij).mono (resource_subset_union _ (C i) W hW) (resource_subset_union _ (C j) X hX)
  · intro e he
    rcases Finset.mem_union.mp he with he|he
    · obtain ⟨W,hW,he⟩ := Finset.mem_biUnion.mp he
      exact Finset.mem_biUnion.mpr ⟨W,Finset.mem_union_left _ hW,he⟩
    · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp he
      obtain ⟨W,hW,he⟩ := Finset.mem_biUnion.mp ((hC i).covers hi)
      exact Finset.mem_biUnion.mpr ⟨W,Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hW⟩),he⟩

end Oberwolfach
