module

public import Oberwolfach.LongPreparationFactorClassification

@[expose] public section
/-! If every factor component is longer than K, there can be no index
assigned to a component of size at most K. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem all_long_components_exclude_short_indices
    {n K:ℕ} (F:SimpleGraph (Fin n)) (J:Type) (C:J→F.ConnectedComponent)
    (hAll:∀v,K<Fintype.card (F.connectedComponentMk v))
    (hshort:∀j,Fintype.card (C j)≤K):IsEmpty J:=by
  constructor
  intro j
  have hlong:K<Fintype.card (C j):=by
    induction (C j) using SimpleGraph.ConnectedComponent.ind with
    | _ v => exact hAll v
  exact (not_lt_of_ge (hshort j)) hlong
end Oberwolfach
