module

public import Oberwolfach.ActualOldDirectedPhysicalHost
public import Oberwolfach.ActualResidualSumIndices

@[expose] public section
/-! With no final marked starts, the directed old-piece embedding places all
of the deleted source edges in the physical host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_old_directed_host_with_empty_final
    {X V A B J:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [DecidableEq B] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=A⊕B) (J:=J) F)
    (hempty:IsEmpty A) (hs:data.s₁=firstSumIndices) (ψ:X→V)
    (P:SimpleGraph V) (Arc:V→V→Prop) (hArc:∀x y,Arc x y→P.Adj x y)
    (hdir:ActualOldImageDirected data ψ Arc):
    data.deletedEdges.image (Sym2.map ψ)⊆P.edgeFinset:=by
  have hS:data.s₁=∅:=by
    rw [hs]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨a,_,_⟩:=Finset.mem_image.mp hi
    exact hempty.false a
  have hFinal:(Finset.univ.biUnion (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset))=∅:=by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨i,_,_⟩:=Finset.mem_biUnion.mp he
    have hi:(i.val:A⊕B)∈(∅:Finset (A⊕B)):=hS ▸ i.property
    exact Finset.notMem_empty _ hi
  have hh:=actual_old_directed_physical_host data ψ P Arc hArc hdir
  simpa only [hFinal,Finset.sdiff_empty] using hh
end Oberwolfach
