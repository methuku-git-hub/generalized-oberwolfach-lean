module

public import Oberwolfach.OrdinaryInducedRimEvent

@[expose] public section
/-! The common sampled cut also supplies every smaller cut parameter and
smaller reference coefficient required by a later correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]

theorem ordinary_induced_rim_cut_smaller_parameter
    (I:Finset V) (A:V→V→ℕ) (α pstar δ href:ℝ)
    (h:OrdinaryInducedRimCutEvent I A α pstar)
    (hδ:δ≤min (α/32) (pstar/512)) (hhref:href≤α*pstar/64):
    ∀S T:Finset I,(1-2*δ)*I.card<(S.card:ℝ)+T.card→
      href*I.card*min (S.card:ℝ) T.card≤(matrixCut (fun x y:I=>A x.val y.val) S T:ℝ):=by
  intro S T hlarge
  have hI:(0:ℝ)≤I.card:=by positivity
  have hm:0≤min (S.card:ℝ) T.card:=le_min (by positivity) (by positivity)
  have hlarger:(1-2*min (α/32) (pstar/512))*I.card<(S.card:ℝ)+T.card:=by
    have hh:=mul_le_mul_of_nonneg_right hδ hI
    nlinarith only [hh,hlarge]
  have hcut:=h S T hlarger
  have hcoef:=mul_le_mul_of_nonneg_right hhref (mul_nonneg hI hm)
  nlinarith only [hcut,hcoef]
end Oberwolfach
