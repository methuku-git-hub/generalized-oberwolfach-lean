module

public import Oberwolfach.ResidualActualData

@[expose] public section
/-! Prescribed residual vertices lie in the restricted old domain whenever
the omitted final interiors are disjoint from the residual domain. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_prescribed_subset_old_without_disjoint_interiors
    {X K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F) (hF:F.IsRegularOfDegree 2)
    (Interiors:Finset X) (hdis:Disjoint Interiors data.remaining):
    data.prescribed⊆data.oldDomain\Interiors:=by
  intro x hx
  apply Finset.mem_sdiff.mpr
  constructor
  · unfold ActualResidualData.oldDomain
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hx))
  · intro hi
    exact Finset.disjoint_left.mp hdis hi ((data.graph_facts hF).2.1 hx)
end Oberwolfach
