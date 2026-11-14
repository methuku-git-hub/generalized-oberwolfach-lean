module

public import Oberwolfach.OrdinaryInducedRimEvent

@[expose] public section
/-! The induced raw rim-cut event supplies any smaller cut coefficient and
    stricter cutoff required by the correction hierarchy. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_induced_rim_cut_event_weaken
    {V:Type} [Fintype V] [LinearOrder V] (I:Finset V) (A:V→V→ℕ) (α pstar δ href:ℝ)
    (hδ:δ≤min (α/32) (pstar/512)) (hh:href≤α*pstar/64)
    (event:OrdinaryInducedRimCutEvent I A α pstar):
    ∀S T:Finset I,(1-2*δ)*I.card<(S.card:ℝ)+T.card→
      href*I.card*min (S.card:ℝ) T.card≤(matrixCut (fun x y:I=>A x.val y.val) S T:ℝ):=by
  intro S T hlarge
  have hn:(0:ℝ)≤I.card:=Nat.cast_nonneg _
  have hs:0≤min (S.card:ℝ) T.card:=by positivity
  have hδn:=mul_le_mul_of_nonneg_right hδ hn
  have hl:(1-2*min (α/32) (pstar/512))*I.card<(S.card:ℝ)+T.card:=by nlinarith only [hlarge,hδn]
  have hc:=event S T hl
  have hcoeff:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hn) hs
  exact hcoeff.trans hc
end Oberwolfach
