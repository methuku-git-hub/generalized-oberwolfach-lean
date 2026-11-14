module

public import Oberwolfach.ResidualActualData

@[expose] public section
/-! Both endpoints of each actual final path are prescribed and belong to
the previously embedded and residual source domains. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_final_path_endpoints_prescribed
    {X K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F)
    (hF:F.IsRegularOfDegree 2) (i:{i // i∈data.s₁}):
    data.start (.inl i)∈data.prescribed ∧ data.finish (.inl i)∈data.prescribed ∧
    data.start (.inl i)∈data.oldDomain ∧ data.finish (.inl i)∈data.oldDomain ∧
    data.start (.inl i)∈data.remaining ∧ data.finish (.inl i)∈data.remaining:=by
  have hs:data.start (.inl i)∈data.prescribed:=by
    apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨i.val,i.property,?_⟩
    change (data.P i.val).getVert 2 ∈ {(data.P i.val).getVert 2,(data.P i.val).getVert (2+data.c*data.d)}
    simp
  have hf:data.finish (.inl i)∈data.prescribed:=by
    apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨i.val,i.property,?_⟩
    change (data.P i.val).getVert (2+data.c*data.d) ∈ {(data.P i.val).getVert 2,(data.P i.val).getVert (2+data.c*data.d)}
    simp
  have hsub:data.prescribed⊆data.remaining:=(data.graph_facts hF).2.1
  refine ⟨hs,hf,?_,?_,hsub hs,hsub hf⟩
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hs))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hf))
end Oberwolfach
