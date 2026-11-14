module

public import Oberwolfach.RandomColourCuts
public import Oberwolfach.InducedFractionalCycles

@[expose] public section
/-! Restricting ambient physical edges to a fixed subtype commutes with
    their sampled orientation and colour, preserving the ambient order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_induced_sampled_colour_orientation
    {V:Type} [LinearOrder V] (P:SimpleGraph V) (I:Finset V) {k:ℕ}
    (σ:Sym2 V→Fin k×Bool) (a:Fin k):
    sampledColourOrientation (P.induce (I:Set V))
      (fun e:Sym2 I=>σ (Sym2.map (⟨Subtype.val,Subtype.val_injective⟩:I↪V) e)) a =
      (fun x y:I=>sampledColourOrientation P σ a x.val y.val):=by
  funext x y
  simp [sampledColourOrientation,orientationBit]

theorem ordinary_induced_sampled_orientation
    {V:Type} [LinearOrder V] (P:SimpleGraph V) (I:Finset V) (σ:Sym2 V→Bool):
    sampledOrientation (P.induce (I:Set V))
      (fun e:Sym2 I=>σ (Sym2.map (⟨Subtype.val,Subtype.val_injective⟩:I↪V) e)) =
      (fun x y:I=>sampledOrientation P σ x.val y.val):=by
  funext x y
  simp [sampledOrientation,orientationBit]
end Oberwolfach
