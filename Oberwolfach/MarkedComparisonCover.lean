module

public import Oberwolfach.MarkedRowCoverPackings

@[expose] public section

/-! A comparison deletion inside the free set suffices to make a new row
cover disjoint from all earlier rows. Physical-map injectivity is used
before applying invariance of the free set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head : E→V} {ktail khead : T→V} {H₀ HK : V→U→Prop}
    {π : Equiv.Perm V} {m b : ℕ}

theorem marked_comparison_cover_disjoint (hm : 1≤m) (hb : 1≤b)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (M N : Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (F : Finset V) (hF : ∀ z,π z∈F ↔ z∈F) (v : V)
    (hM : ∀ W∈M,v∉markedWheelRows W)
    (hN : ∀ W∈N,markedWheelRows W⊆insert v F)
    (hD : ∀ W∈N,Disjoint (markedWheelRimGraph W) (spanningRestriction (markedPackingRimGraph M) F))
    (hJ : ∀ x u,markedPackingSpokes N x u→¬(x∈F ∧ markedPackingSpokes M x u)) :
    Disjoint (N.biUnion markedWheelPhysicalResources) (M.biUnion markedWheelPhysicalResources) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨W,hW,he⟩ := Finset.mem_biUnion.mp he
  obtain ⟨Z,hZ,hf⟩ := Finset.mem_biUnion.mp hf
  have hZs : markedWheelRows Z⊆(Finset.univ.erase v) := by
    intro z hz
    exact Finset.mem_erase.mpr ⟨fun h=>hM Z hZ (h ▸ hz),Finset.mem_univ _⟩
  have hs := marked_resource_supported_inter hp (Finset.univ.erase v) (insert v F) e
    (marked_wheel_resources_supported Z _ hZs e hf) (marked_wheel_resources_supported W _ (hN W hW) e he)
  have hsub : (Finset.univ.erase v)∩insert v F⊆F := by
    intro z hz
    obtain ⟨hz₁,hz₂⟩ := Finset.mem_inter.mp hz
    rcases Finset.mem_insert.mp hz₂ with rfl|hzF
    · exact False.elim (Finset.notMem_erase _ _ hz₁)
    · exact hzF
  have hfree := marked_supported_resource_is_free F hF e (marked_resource_support_mono hsub e hs)
  cases e with
  | inr xu=>
    obtain ⟨hu,hx⟩ := (markedWheelPhysicalResources_spoke W xu.1 xu.2).mp he
    obtain ⟨hu',hx'⟩ := (markedWheelPhysicalResources_spoke Z xu.1 xu.2).mp hf
    exact hJ xu.1 xu.2 ⟨W,hW,hu,hx⟩ ⟨hfree,Z,hZ,hu',hx'⟩
  | inl e=>
    have he' := (markedWheelPhysicalResources_rim W e).mp he
    have hf' := (markedWheelPhysicalResources_rim Z e).mp hf
    have hcard : e.card=2 := by
      obtain ⟨a,_,ha⟩ := Finset.mem_image.mp he'
      rw [←ha]
      exact markedCycle_physical_edge_card tail head ktail khead m π b hm hb W.1 a
    obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp hcard
    have hxF : x∈F := hfree (by simp)
    have hyF : y∈F := hfree (by simp)
    have hMD : (spanningRestriction (markedPackingRimGraph M) F).Adj x y :=
      (spanningRestriction_adj _ _ _ _).mpr
        ⟨⟨hxy,Finset.mem_biUnion.mpr ⟨Z,hZ,hf'⟩⟩,hxF,hyF⟩
    exact disjoint_graphs_no_common_edge _ _ (hD W hW) x y ⟨hxy,he'⟩ hMD

end Oberwolfach
