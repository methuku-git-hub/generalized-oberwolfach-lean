module

public import Oberwolfach.MarkedBoundaryRemainder

@[expose] public section

/-! Boundary coverage is translated back to the original typed arc and
spoke sets. The uncovered graph is supported on the inner row/hub pair and
has exactly the physical resource complement, without assuming global divisibility. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T:Type} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq T]
    {tail head:E→V} {ktail khead:T→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

theorem marked_boundary_remainder_support
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hH:∀ v u,¬(H₀ v u∧HK v u)) (X:Finset V) (Z:Finset U)
    (A:Finset (E⊕T)) (S:Finset (V×U))
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hM:∀ W∈M,∀ W'∈M,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))
    (hA:M.biUnion markedWheelArcs⊆A) (hS:M.biUnion markedWheelSpokePairs⊆S)
    (hArcs:∀ a∈A,Sum.elim tail ktail a∉X∨Sum.elim head khead a∉X→
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈M.biUnion markedWheelPhysicalResources)
    (hSpokes:∀ s∈S,s.1∉X∨s.2∉Z→Sum.inr s∈M.biUnion markedWheelPhysicalResources):
    let A':=A\M.biUnion markedWheelArcs
    let S':=S\M.biUnion markedWheelSpokePairs
    (∀ a∈A',Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)∧
      (∀ s∈S',s.1∈X∧s.2∈Z)∧
      (A'.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S'.image Sum.inr)=
        (A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr)\
          M.biUnion markedWheelPhysicalResources:=by
  dsimp only
  have ha (a:E⊕T):a∈M.biUnion markedWheelArcs↔
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈M.biUnion markedWheelPhysicalResources:=by
    simp only [Finset.mem_biUnion,markedWheel_arc_resource_iff hp]
  have hs (s:V×U):s∈M.biUnion markedWheelSpokePairs↔Sum.inr s∈M.biUnion markedWheelPhysicalResources:=by
    simp only [Finset.mem_biUnion,markedWheel_spoke_resource]
  refine ⟨?_,?_,?_⟩
  · intro a ha'
    obtain ⟨haA,haM⟩:=Finset.mem_sdiff.mp ha'
    constructor
    · by_contra hn;exact haM ((ha a).mpr (hArcs a haA (Or.inl hn)))
    · by_contra hn;exact haM ((ha a).mpr (hArcs a haA (Or.inr hn)))
  · intro s hs'
    obtain ⟨hsS,hsM⟩:=Finset.mem_sdiff.mp hs'
    constructor
    · by_contra hn;exact hsM ((hs s).mpr (hSpokes s hsS (Or.inl hn)))
    · by_contra hn;exact hsM ((hs s).mpr (hSpokes s hsS (Or.inr hn)))
  · ext e
    cases e with
    | inl e=>
      simp only [Finset.mem_union,Finset.mem_image,Sum.inl.injEq,Sum.inr_ne_inl,and_false,
        exists_false,or_false,Finset.mem_sdiff]
      constructor
      · rintro ⟨a,⟨haA,haM⟩,rfl⟩
        exact ⟨⟨a,haA,rfl⟩,fun h=>haM ((ha a).mpr h)⟩
      · rintro ⟨⟨a,haA,rfl⟩,haM⟩
        exact ⟨a,⟨haA,fun h=>haM ((ha a).mp h)⟩,rfl⟩
    | inr s=>
      simp only [Finset.mem_union,Finset.mem_image,Sum.inl_ne_inr,and_false,exists_false,
        false_or,Sum.inr.injEq,exists_eq_right,Finset.mem_sdiff,hs]

end Oberwolfach
