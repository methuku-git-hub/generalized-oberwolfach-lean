module

public import Oberwolfach.ResourceDecompositions

@[expose] public section
/-! Glue disjoint decompositions whose pieces have different types. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem resource_decomposition_sum_with_packing
    {E W Z C:Type} [DecidableEq E] [DecidableEq W] [DecidableEq Z] [DecidableEq C]
    (R:W→Finset E) (B:Z→Finset E) (lift:C→Z) (S:Finset E) (M:Finset C)
    (hS:HasResourceDecomposition R S)
    (hM:∀a∈M,∀b∈M,a≠b→Disjoint (B (lift a)) (B (lift b)))
    (hdis:Disjoint S (M.biUnion fun c=>B (lift c))):
    HasResourceDecomposition (Sum.elim R B) (S∪M.biUnion fun c=>B (lift c)) := by
  have hsample:HasResourceDecomposition (Sum.elim R B) S:=
    resource_decomposition_map R (Sum.elim R B) Sum.inl (by intro w; rfl) S hS
  have hpacked:HasResourceDecomposition (fun c=>B (lift c)) (M.biUnion fun c=>B (lift c)):=
    ⟨M,hM,rfl⟩
  have hsum:HasResourceDecomposition (Sum.elim R B) (M.biUnion fun c=>B (lift c)):=
    resource_decomposition_map (fun c=>B (lift c)) (Sum.elim R B) (fun c=>Sum.inr (lift c))
      (by intro c; rfl) _ hpacked
  exact resource_decomposition_union (Sum.elim R B) _ _ hsample hsum hdis
end Oberwolfach
