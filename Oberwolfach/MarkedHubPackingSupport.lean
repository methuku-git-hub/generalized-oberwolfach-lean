module

public import Oberwolfach.MarkedRowCoverPackings

@[expose] public section

/-! Recover row and hub support from the exact spoke-union conclusion of
the proved hub-cover theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head : E→V} {ktail khead : T→V} {H₀ HK : V→U→Prop}
    {π : Equiv.Perm V} {m b n : ℕ}

theorem marked_hub_cover_support
    (M : Finset (MarkedWheel tail head ktail khead m π b H₀ HK)) (u : Fin n→U)
    (hcover : M.biUnion markedWheelPhysicalResources=(markedPackingRims M).image Sum.inl∪
      Finset.univ.biUnion (fun i=>(Finset.univ.filter (fun v=>H₀ v (u i)∨HK v (u i))).image (fun v=>Sum.inr (v,u i))))
    (F : Finset V) (hF : ∀ z,π z∈F ↔ z∈F)
    (hneighbours : ∀ i x,H₀ x (u i)∨HK x (u i)→x∈F) :
    (∀ W∈M,W.2.val∈Finset.univ.image u) ∧
    (∀ W∈M,markedWheelRows W⊆F) ∧ GraphSupportedOn F (markedPackingRimGraph M) := by
  have hhub (W) (hW : W∈M) : W.2.val∈Finset.univ.image u := by
    have he : Sum.inr (W.1.val 0,W.2.val)∈M.biUnion markedWheelPhysicalResources :=
      Finset.mem_biUnion.mpr ⟨W,hW,(markedWheelPhysicalResources_spoke W _ _).mpr
        ⟨rfl,Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩⟩⟩
    rw [hcover] at he
    rcases Finset.mem_union.mp he with he|he
    · obtain ⟨e,_,he⟩ := Finset.mem_image.mp he
      cases he
    · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp he
      obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hi
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,(Prod.mk.inj (Sum.inr.inj he)).2⟩
  have hrows (W) (hW : W∈M) : markedWheelRows W⊆F := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (hhub W hW)
    intro x hx
    have he := markedWheelPhysicalResources_spoke_present W x W.2.val
      ((markedWheelPhysicalResources_spoke W x W.2.val).mpr ⟨rfl,hx⟩)
    rw [←hi] at he
    exact hneighbours i x he
  refine ⟨hhub,hrows,?_⟩
  intro x y hxy
  obtain ⟨W,hW,he⟩ := Finset.mem_biUnion.mp hxy.2
  have hs := markedWheelRimGraph_supported W x y ⟨hxy.1,he⟩
  have hsub : markedWheelRows W∪(markedWheelRows W).image π⊆F := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz|hz
    · exact hrows W hW hz
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
      exact (hF a).mpr (hrows W hW ha)
  exact ⟨hsub hs.1,hsub hs.2⟩

end Oberwolfach
