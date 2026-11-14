module

public import Oberwolfach.OrdinarySampleEditDegrees

@[expose] public section
/-! The sampled minimum spoke degree survives a bounded row edit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_edited_spoke_degree_from_sample (H₀ H:V→U→Prop) (β₀ β ξ d:ℝ)
    (hparent:∀v,β₀*Fintype.card V≤((Finset.univ.filter (H₀ v)).card:ℝ))
    (hRow:∀v,((changed (Finset.univ.filter (H₀ v)) (Finset.univ.filter (H v))).card:ℝ)≤d)
    (hscale:d≤ξ*Fintype.card V) (hmargin:β+ξ≤β₀):
    ∀v,β*Fintype.card V≤((Finset.univ.filter (H v)).card:ℝ):=by
  intro v
  let A:=Finset.univ.filter (H₀ v)
  let B:=Finset.univ.filter (H v)
  have hdiff:(A.card:ℝ)-(B.card:ℝ)≤(changed A B).card:=
    (le_abs_self _).trans (card_difference_le_changed A B)
  have hp:β₀*Fintype.card V≤(A.card:ℝ):=by
    convert hparent v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have he:((changed A B).card:ℝ)≤d:=by
    convert hRow v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hm:=mul_le_mul_of_nonneg_right hmargin (Nat.cast_nonneg (Fintype.card V): (0:ℝ)≤_)
  have ht:β*Fintype.card V≤(B.card:ℝ):=by nlinarith only [hdiff,hp,he,hscale,hm]
  convert ht using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
