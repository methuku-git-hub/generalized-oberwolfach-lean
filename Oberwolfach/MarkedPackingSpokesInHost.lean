module

public import Oberwolfach.MarkedWheelFiniteBalance

@[expose] public section
/-! Every spoke used by a marked wheel belongs to one of its two typed
spoke relations. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {m b:ℕ} {H₀ HK:V→U→Prop}
theorem marked_packing_spokes_subset_host
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK)):
    M.biUnion markedWheelSpokePairs ⊆ Finset.univ.filter (fun z:V×U=>H₀ z.1 z.2∨HK z.1 z.2):=by
  intro z hz
  obtain ⟨W,_,hz⟩:=Finset.mem_biUnion.mp hz
  obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hz
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  refine Fin.cases ?_ (fun j=>?_) i
  · exact Or.inr W.2.property.1
  · exact Or.inl (W.2.property.2 j)
theorem marked_packing_disjoint_exclusions_give_host_subsets
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (A:Finset (E⊕K)) (S:Finset (V×U))
    (hA:Disjoint A (M.biUnion markedWheelArcs))
    (hS:Disjoint S (M.biUnion markedWheelSpokePairs)):
    M.biUnion markedWheelArcs⊆Finset.univ\A ∧
    M.biUnion markedWheelSpokePairs⊆
      (Finset.univ.filter (fun z:V×U=>H₀ z.1 z.2∨HK z.1 z.2))\S:=by
  constructor
  · intro a ha
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun h=>Finset.disjoint_left.mp hA h ha⟩
  · intro z hz
    exact Finset.mem_sdiff.mpr ⟨marked_packing_spokes_subset_host M hz,fun h=>Finset.disjoint_left.mp hS h hz⟩
end Oberwolfach
