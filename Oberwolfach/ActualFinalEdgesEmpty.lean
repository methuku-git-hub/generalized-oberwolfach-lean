module

public import Oberwolfach.ActualResidualSumIndices

@[expose] public section
/-! No first-summand indices means the final-path edge set is empty. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_final_edges_empty_of_empty_first_index
    {X A B J:Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [DecidableEq B] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=A⊕B) (J:=J) F)
    (hempty:IsEmpty A) (hs:data.s₁=firstSumIndices):
    (Finset.univ.biUnion (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset))=∅:=by
  have hS:data.s₁=∅:=by
    rw [hs]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨a,_,_⟩:=Finset.mem_image.mp hi
    exact hempty.false a
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨i,_,_⟩:=Finset.mem_biUnion.mp he
  have hi:(i.val:A⊕B)∈(∅:Finset (A⊕B)):=hS ▸ i.property
  exact Finset.notMem_empty _ hi
end Oberwolfach
