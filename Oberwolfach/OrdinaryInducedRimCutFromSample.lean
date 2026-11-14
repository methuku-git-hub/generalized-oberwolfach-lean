module

public import Oberwolfach.OrdinaryInducedRimCutNormalize
public import Oberwolfach.OrdinaryInducedRimCutEdits
public import Oberwolfach.OrdinaryNearBalanceCutWeaken

@[expose] public section
/-! Actual sample matrix cuts and bounded cleanup edits construct the
    orientation and induced rim cut needed by sparse correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]

theorem ordinary_induced_rim_cut_from_sample_and_edits
    (Qraw Q:SimpleGraph V) (I:Finset V) (coins:Sym2 V→Bool) (δ h ζ L htarget:ℝ)
    (hI:0<I.card) (hζ:0≤ζ) (hscale:L≤ζ*I.card) (hmargin:2*htarget≤h-ζ)
    (hedit:∀v,((changed (Qraw.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L)
    (hmat:∀S T:Finset I,(1-2*δ)*I.card<(S.card:ℝ)+T.card→
      h*I.card*min (S.card:ℝ) T.card≤
        (matrixCut (fun x y:I=>sampledOrientation Qraw coins x.val y.val) S T:ℝ)):
    ∃R:I→I→Prop,
      (∀x y,relationMultiplicity R x y+relationMultiplicity R y x=if (Q.induce (I:Set V)).Adj x y then 1 else 0) ∧
      BipartiteLargeCut (relationMultiplicity R) δ (2*htarget):=by
  have hc:=ordinary_induced_rim_matrix_cut_normalized I (sampledOrientation Qraw coins) δ h hI hmat
  have he:=ordinary_induced_rim_cut_after_edits Qraw Q I coins δ h ζ L hI hζ hscale hedit hc
  let localCoins:=fun e:Sym2 I=>coins (Sym2.map (⟨Subtype.val,Subtype.val_injective⟩:I↪V) e)
  let R:=ordinarySampledOrientedRelation (Q.induce (I:Set V)) localCoins
  refine ⟨R,he.1,?_⟩
  exact ordinary_large_cut_weaken (relationMultiplicity R) δ (h-ζ) (2*htarget) hmargin he.2
end Oberwolfach
