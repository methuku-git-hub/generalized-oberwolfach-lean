module

public import Oberwolfach.OrdinaryVortexBufferedRootRestrictionGeometry

@[expose] public section
/-! A buffered root-size estimate pays both root-free cleanup margins once
its coefficient has been chosen after the sampling rate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_free_cleanup_card_margins_before_sampling
    (T:Finset V) (W:Finset U) (lam βe βh:ℝ)
    (hlam:0≤lam) (he:0≤βe) (hh:0≤βh)
    (hroot:(T.card:ℝ)+W.card≤lam*Fintype.card V)
    (hrow:lam≤βe/4) (hhub:lam≤βh/2):
    (T.card:ℝ)≤(βe/4)*Fintype.card (V⊕U) ∧
    (W.card:ℝ)≤(βh/2)*Fintype.card (V⊕U):=by
  have hn:(Fintype.card V:ℝ)≤Fintype.card (V⊕U):=by
    exact_mod_cast (Fintype.card_le_of_injective (Sum.inl:V→V⊕U) Sum.inl_injective)
  have hn0:0≤(Fintype.card V:ℝ):=Nat.cast_nonneg _
  have hT:0≤(T.card:ℝ):=Nat.cast_nonneg _
  have hW:0≤(W.card:ℝ):=Nat.cast_nonneg _
  have hr:=mul_le_mul_of_nonneg_right hrow hn0
  have hu:=mul_le_mul_of_nonneg_right hhub hn0
  have hr2:=mul_le_mul_of_nonneg_left hn (show 0≤βe/4 by positivity)
  have hu2:=mul_le_mul_of_nonneg_left hn (show 0≤βh/2 by positivity)
  constructor <;> linarith
end Oberwolfach
