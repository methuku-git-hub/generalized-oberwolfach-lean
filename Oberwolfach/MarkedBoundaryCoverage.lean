module

public import Oberwolfach.MarkedBoundaryRemainder

@[expose] public section

/-! Exact incoming, outgoing and spoke incidence lists account for every
boundary edge, including both typed copies when their auxiliary label
coincides. The remaining finite host inherits divisibility. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T J I:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype T]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq T]
    {tail head:E→V} {ktail khead:T→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

theorem marked_boundary_coverage_from_incidence_lists
    (X:Finset V) (Z:Finset U) (root:J→V) (hub:I→U)
    (hroots:∀ v∉X,∃ j,root j=v) (hhubs:∀ u∉Z,∃ i,hub i=u)
    (A₀ A₁ X₀ X₁:J→Finset V) (Y₀ Y₁:J→Finset U) (Y:I→Finset V)
    (incoming:∀ j,(A₀ j⊕A₁ j)→E⊕T) (outgoing:∀ j,(X₀ j⊕X₁ j)→E⊕T)
    (hin:∀ j a,Sum.elim head khead a=root j→∃ w,incoming j w=a)
    (hout:∀ j a,Sum.elim tail ktail a=root j→∃ w,outgoing j w=a)
    (hrow:∀ j u,H₀ (root j) u∨HK (root j) u→u∈Y₀ j∪Y₁ j)
    (hcol:∀ i v,H₀ v (hub i)∨HK v (hub i)→v∈Y i)
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hMi:∀ j a,Sum.inl (markedPhysicalEdge tail head ktail khead π (incoming j a))∈M.biUnion markedWheelPhysicalResources)
    (hMo:∀ j a,Sum.inl (markedPhysicalEdge tail head ktail khead π (outgoing j a))∈M.biUnion markedWheelPhysicalResources)
    (hMr:∀ j u,u∈Y₀ j∪Y₁ j→Sum.inr (root j,u)∈M.biUnion markedWheelPhysicalResources)
    (hMh:∀ i v,v∈Y i→Sum.inr (v,hub i)∈M.biUnion markedWheelPhysicalResources):
    (∀ a:E⊕T,Sum.elim tail ktail a∉X∨Sum.elim head khead a∉X→
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈M.biUnion markedWheelPhysicalResources)∧
    (∀ v u,H₀ v u∨HK v u→v∉X∨u∉Z→Sum.inr (v,u)∈M.biUnion markedWheelPhysicalResources):=by
  constructor
  · intro a ha
    rcases ha with ht|hh
    · obtain ⟨j,hj⟩:=hroots _ ht
      obtain ⟨w,rfl⟩:=hout j a hj.symm
      exact hMo j w
    · obtain ⟨j,hj⟩:=hroots _ hh
      obtain ⟨w,rfl⟩:=hin j a hj.symm
      exact hMi j w
  · intro v u hH hu
    rcases hu with hv|hu
    · obtain ⟨j,rfl⟩:=hroots v hv
      exact hMr j u (hrow j u hH)
    · obtain ⟨i,rfl⟩:=hhubs u hu
      exact hMh i v (hcol i v hH)

theorem marked_full_host_boundary_remainder
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hH:∀ v u,¬(H₀ v u∧HK v u)) (X:Finset V) (Z:Finset U)
    (hAS:MarkedRemainderDivisible tail head ktail khead HK Finset.univ
      (Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)) m)
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hM:∀ W∈M,∀ W'∈M,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))
    (hArcs:∀ a:E⊕T,Sum.elim tail ktail a∉X∨Sum.elim head khead a∉X→
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈M.biUnion markedWheelPhysicalResources)
    (hSpokes:∀ v u,H₀ v u∨HK v u→v∉X∨u∉Z→Sum.inr (v,u)∈M.biUnion markedWheelPhysicalResources):
    let A':=Finset.univ\M.biUnion markedWheelArcs
    let S':=(Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2))\M.biUnion markedWheelSpokePairs
    MarkedRemainderDivisible tail head ktail khead HK A' S' m∧
      (∀ a∈A',Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)∧
      (∀ s∈S',s.1∈X∧s.2∈Z)∧
      (A'.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S'.image Sum.inr)=
        (Finset.univ.image (fun a:E⊕T=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪
          (Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)).image Sum.inr)\
          M.biUnion markedWheelPhysicalResources:=by
  apply marked_boundary_remainder hp hH X Z _ _ hAS M hM (Finset.subset_univ _)
  · intro s hs
    obtain ⟨W,hW,hs⟩:=Finset.mem_biUnion.mp hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,markedWheelPhysicalResources_spoke_present W _ _
      ((markedWheel_spoke_resource W s).mp hs)⟩
  · intro a _ ha;exact hArcs a ha
  · intro s hs hn;exact hSpokes s.1 s.2 (Finset.mem_filter.mp hs).2 hn

end Oberwolfach
