module

public import Oberwolfach.MarkedFreeCycleFamilies
public import Oberwolfach.MarkedCycleFamilyFreshHubs
public import Oberwolfach.MarkedCrossFamilyPacking
public import Oberwolfach.ResourceFamilyIndicators

@[expose] public section

/-! A genuine disjoint marked-wheel family, with actual globally injective
row and hub maps and its resulting resource decomposition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K I:Type} [Fintype V] [Fintype U] [Fintype I]
    [DecidableEq V] [DecidableEq U] [DecidableEq I]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_free_wheel_families
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (v₀:V) (W Z:Finset V) (B:Finset U)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hbudget:(W.card:ℝ)+(Fintype.card I*(l+5)+Z.card+l+13)*(2*b+1)<c)
    (hB:(B.card:ℝ)+Fintype.card I<ch):
    ∃ C:I→MarkedWheel tail head ktail khead (l+4) π b H₀ HK,
      Function.Injective (fun z:I×Fin (l+5)=>(C z.1).1.val z.2)∧
      Function.Injective (fun i=>(C i).2.val)∧
      (∀ i,(C i).2.val∉B)∧
      (∀ i k,(C i).1.val k∉W∧(C i).1.val k∉Z∧∀ z∈Z,¬PermutationClose π b ((C i).1.val k) z)∧
      (∀ i j k k',((i,k):I×Fin (l+5))≠(j,k')→¬PermutationClose π b ((C i).1.val k) ((C j).1.val k'))∧
      (∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j)))∧
      HasResourceDecomposition (fun C:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources C) (Finset.univ.biUnion (fun i=>markedWheelPhysicalResources (C i))):=by
  obtain ⟨D,hD,hdis,hsep⟩:=marked_free_cycle_families (I:=I) Q hl v₀ W Z hbudget
  obtain ⟨h,hh,hH⟩:=marked_cycle_family_fresh_hubs Q D B hB
  let C:I→MarkedWheel tail head ktail khead (l+4) π b H₀ HK:=fun i=>⟨D i,⟨h i,hH i⟩⟩
  have hpack:∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j)):=by
    intro i j hij
    have hn:∀ k k',(D i).val k≠(D j).val k':=by
      intro k k' he
      exact Finset.disjoint_left.mp (hdis i j hij) (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩)
        (Finset.mem_image.mpr ⟨k',Finset.mem_univ _,he.symm⟩)
    exact marked_wheels_disjoint_of_shared_labels hp (C i) (C j) ∅
      (fun k k' he=>False.elim (hn k k' he)) (by simp) (fun k k' he=>False.elim (hn k k' he))
  refine ⟨C,?_,h.injective,hh,hD,hsep,hpack,?_⟩
  · rintro ⟨i,k⟩ ⟨j,k'⟩ he
    by_contra hne
    exact hsep i j k k' hne (Or.inl he)
  · exact resource_indexed_family_decomposition markedWheelPhysicalResources C hpack

end Oberwolfach
