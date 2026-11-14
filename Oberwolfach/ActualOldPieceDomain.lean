module

public import Oberwolfach.ActualOldPiecePaths

@[expose] public section
/-! The combined old-piece domain is exactly the union of all actual selected
run vertices and selected cycle vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_old_piece_domain_eq
    {X K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G):
    (Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset))=
      (Finset.univ.biUnion (fun r:SelectedRunIndex data.s₂ data.d data.T=>(data.path (.inr r)).support.toFinset)) ∪
        data.t.biUnion (fun j=>(data.C j).support.toFinset):=by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨z,_,hz⟩:=Finset.mem_biUnion.mp hx
    cases z with
    | inl j =>
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨j.val,j.property,?_⟩
      rw [←cycle_tail_support_eq G (data.C j.val) (data.hcycle j.val j.property)]
      exact hz
    | inr r =>
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨r,Finset.mem_univ _,hz⟩)
  · intro hx
    rcases Finset.mem_union.mp hx with hr | hc
    · obtain ⟨r,_,hr⟩:=Finset.mem_biUnion.mp hr
      exact Finset.mem_biUnion.mpr ⟨.inr r,Finset.mem_univ _,hr⟩
    · obtain ⟨j,hj,hc⟩:=Finset.mem_biUnion.mp hc
      apply Finset.mem_biUnion.mpr
      refine ⟨.inl ⟨j,hj⟩,Finset.mem_univ _,?_⟩
      change x∈(data.C j).tail.support.toFinset
      rw [cycle_tail_support_eq G (data.C j) (data.hcycle j hj)]
      exact hc
end Oberwolfach
