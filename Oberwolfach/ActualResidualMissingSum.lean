module

public import Oberwolfach.ResidualActualData
public import Oberwolfach.ActualResidualSumIndices

@[expose] public section
/-! Read the second-summand residual missing count as a sum over the
original approximate-interval indices. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_residual_missing_sum_second_indices
    {V A B J:Type} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq A] [DecidableEq B] [DecidableEq J]
    {F:SimpleGraph V} (a:ActualResidualData (K:=A⊕B) (J:=J) F)
    (hs:a.s₂=secondSumIndices):
    (∑i∈a.s₂,(a.d-(a.T i).card))=∑b:B,(a.d-(a.T (.inr b)).card):=by
  rw [hs]
  unfold secondSumIndices
  rw [Finset.sum_image]
  intro x hx y hy h
  exact Sum.inr.inj h
end Oberwolfach
