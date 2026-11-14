module

public import Oberwolfach.MarkedPhysicalDeletionRestriction
public import Oberwolfach.MarkedEmptyPhysicalDeletion

@[expose] public section
/-! Physical change graphs avoiding a fixed pair preserve the full restricted
raw sample and both spoke relations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_raw_pair_unchanged_from_graphs
    {W Z : Type} [Fintype W] [Fintype Z] [LinearOrder W] [DecidableEq Z]
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (I:Finset V) (J:Finset U)
    (hR:∀ x∈I,∀ y∈I,¬DR.Adj x y)
    (hS:∀ x∈I,∀ u∈J,¬DS.Adj (Sum.inl x) (Sum.inr u))
    (f:W→V) (g:Z→U) (hf:∀ x,f x∈I) (hg:∀ u,g u∈J):
    rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset)=rawMarkedRestrictPair f g σ ∧
    (fun b x u=>markedDeletePhysicalSpokes H DS b (f x) (g u))=
      (fun b x u=>H b (f x) (g u)) :=by
  have hr:DR.comap f=⊥:=by
    ext x y
    exact iff_false_intro (hR (f x) (hf x) (f y) (hf y))
  constructor
  · rw [rawMarkedRestrictPair_deleteRims,SimpleGraph.edgeFinset_eq_empty.mpr hr,rawMarkedDeleteRims_empty]
  · funext b x u
    simp only [markedDeletePhysicalSpokes,hS (f x) (hf x) (g u) (hg u),not_false_eq_true,and_true]
end Oberwolfach
