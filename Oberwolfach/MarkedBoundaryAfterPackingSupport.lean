module

public import Oberwolfach.MarkedBoundaryRemainderSupport
public import Oberwolfach.MarkedBoundaryAfterPacking
public import Oberwolfach.MarkedPackingUnions
public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section

/-! The final boundary packing is added to the preceding packing using
physical disjointness. Its incidence lists need cover only the edges that
remain after the preceding packing. All four divisibility equations are
then inherited by the exact typed remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K J I:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
    {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

theorem marked_boundary_remainder_after_packing_support
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hH:∀ v u,¬(H₀ v u∧HK v u)) (X:Finset V) (Z:Finset U)
    (M N:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hM:∀ W∈M,∀ W'∈M,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))
    (hN:∀ W∈N,∀ W'∈N,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))
    (hMN:Disjoint (M.biUnion markedWheelPhysicalResources) (N.biUnion markedWheelPhysicalResources))
    (root:J→V) (hub:I→U) (hroots:∀ v∉X,∃ j,root j=v) (hhubs:∀ u∉Z,∃ i,hub i=u)
    (hrows:∀ j a,Sum.elim tail ktail a=root j∨Sum.elim head khead a=root j→
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∉M.biUnion markedWheelPhysicalResources→
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈N.biUnion markedWheelPhysicalResources)
    (hspokes:∀ j u,H₀ (root j) u∨HK (root j) u→
      Sum.inr (root j,u)∉M.biUnion markedWheelPhysicalResources→
      Sum.inr (root j,u)∈N.biUnion markedWheelPhysicalResources)
    (hcolumns:∀ i v,H₀ v (hub i)∨HK v (hub i)→
      Sum.inr (v,hub i)∉M.biUnion markedWheelPhysicalResources→
      Sum.inr (v,hub i)∈N.biUnion markedWheelPhysicalResources)
:
    let P:=M∪N
    (∀ W∈P,∀ W'∈P,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))∧
    (let A':=Finset.univ\P.biUnion markedWheelArcs
     let S':=(Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2))\P.biUnion markedWheelSpokePairs
     (∀ a∈A',Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)∧
       (∀ s∈S',s.1∈X∧s.2∈Z)∧
       (A'.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S'.image Sum.inr)=
         (Finset.univ.image (fun a:E⊕K=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪
           (Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)).image Sum.inr)\
           P.biUnion markedWheelPhysicalResources):=by
  let P:=M∪N
  have hP:∀ W∈P,∀ W'∈P,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'):=by
    intro W hW W' hW' hne
    rcases Finset.mem_union.mp hW with hW|hW <;> rcases Finset.mem_union.mp hW' with hW'|hW'
    · exact hM W hW W' hW' hne
    · exact hMN.mono (resource_subset_union _ M W hW) (resource_subset_union _ N W' hW')
    · exact hMN.symm.mono (resource_subset_union _ N W hW) (resource_subset_union _ M W' hW')
    · exact hN W hW W' hW' hne
  refine ⟨hP,?_⟩
  apply marked_boundary_remainder_support hp hH X Z _ _ P hP (Finset.subset_univ _)
  · intro z hz
    obtain ⟨W,hW,hz⟩:=Finset.mem_biUnion.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,markedWheelPhysicalResources_spoke_present W z.1 z.2
      ((markedWheel_spoke_resource W z).mp hz)⟩
  · intro a _ ha
    rw [show P.biUnion markedWheelPhysicalResources=M.biUnion markedWheelPhysicalResources∪
      N.biUnion markedWheelPhysicalResources from Finset.union_biUnion]
    by_cases h:Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈M.biUnion markedWheelPhysicalResources
    · exact Finset.mem_union_left _ h
    · apply Finset.mem_union_right
      rcases ha with ht|hh
      · obtain ⟨j,hj⟩:=hroots _ ht
        exact hrows j a (Or.inl hj.symm) h
      · obtain ⟨j,hj⟩:=hroots _ hh
        exact hrows j a (Or.inr hj.symm) h
  · intro z hz hzout
    have hsp:=(Finset.mem_filter.mp hz).2
    rw [show P.biUnion markedWheelPhysicalResources=M.biUnion markedWheelPhysicalResources∪
      N.biUnion markedWheelPhysicalResources from Finset.union_biUnion]
    by_cases h:Sum.inr z∈M.biUnion markedWheelPhysicalResources
    · exact Finset.mem_union_left _ h
    · apply Finset.mem_union_right
      rcases hzout with hv|hu
      · obtain ⟨j,hj⟩:=hroots _ hv
        have hh:=hspokes j z.2 (by simpa only [hj] using hsp) (by simpa only [hj] using h)
        simpa only [hj] using hh
      · obtain ⟨i,hi⟩:=hhubs _ hu
        have hh:=hcolumns i z.1 (by simpa only [hi] using hsp) (by simpa only [hi] using h)
        simpa only [hi] using hh

end Oberwolfach
