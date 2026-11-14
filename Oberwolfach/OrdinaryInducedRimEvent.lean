module

public import Oberwolfach.OrdinaryInducedOrientationCommutation
public import Oberwolfach.GraphCuts

@[expose] public section
/-! Matrix cut data for the restriction of one ambient orientation to a
    fixed inner vertex set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryInducedRimCutEvent {V:Type} [Fintype V] [LinearOrder V]
    (I:Finset V) (A:V→V→ℕ) (α pstar:ℝ):Prop:=
  ∀S T:Finset I,
    (1-2*min (α/32) (pstar/512))*I.card<(S.card:ℝ)+T.card→
    (α*pstar/64)*I.card*min (S.card:ℝ) T.card≤(matrixCut (fun x y:I=>A x.val y.val) S T:ℝ)
end Oberwolfach
