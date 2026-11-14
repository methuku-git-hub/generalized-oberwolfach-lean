module

public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! The current factor's used images and unembedded component vertices share
one source-vertex budget; saturated labels are counted separately. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem prescribed_embedding_label_budget {V:Type} [DecidableEq V]
    (A S:Finset V) (q:ℕ) (t δ n:ℝ)
    (hsource:(A.card:ℝ)+q≤δ*n) (hsaturated:(S.card:ℝ)≤t):
    (((A∪S).card:ℕ):ℝ)+(q+1:ℕ)≤t+δ*n+1 := by
  have hh:((A∪S).card:ℝ)≤(A.card:ℝ)+S.card:=by
    exact_mod_cast Finset.card_union_le A S
  push_cast
  linarith
end Oberwolfach
