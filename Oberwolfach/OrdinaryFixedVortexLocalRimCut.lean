module

public import Oberwolfach.OrdinaryFixedVortexRimCutTransport
public import Oberwolfach.OrdinaryInducedRimCutSmallerParameter

@[expose] public section
/-! Transport the common oriented cut to a vortex level and allow the
smaller cut parameter chosen for the nonroot construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_fixed_vortex_local_rim_cut
    (P:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (σ:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool) (i:ℕ) (α pstar δ href:ℝ)
    (h:OrdinaryInducedRimCutEvent (Q.extendedVertices (i+1))
      (sampledOrientation (rawWheelGraph P σ) coins) α pstar)
    (hδ:δ≤min (α/32) (pstar/512)) (hhref:href≤α*pstar/64):
    let f:markedVortexVertexType Q i↪V:=(markedVortexVertexEmbedding Q i).toEmbedding;
    let g:=markedVortexHubEmbedding Q i;let I:=markedVortexInnerVertices Q i;
    let localRaw:=ordinaryRawRestrictPair f g σ;
    let localCoins:=fun e:Sym2 (markedVortexVertexType Q i)=>coins (Sym2.map f e);
    ∀S T:Finset I,(1-2*δ)*I.card<(S.card:ℝ)+T.card→
      href*I.card*min (S.card:ℝ) T.card≤
        (matrixCut (fun x y:I=>sampledOrientation (rawWheelGraph (P.comap f) localRaw) localCoins x.val y.val) S T:ℝ):=by
  intro f g I localRaw localCoins
  have hc:=ordinary_fixed_vortex_rim_cut_transport P D m β ε Q σ coins i α pstar h
  exact ordinary_induced_rim_cut_smaller_parameter I _ α pstar δ href hc hδ hhref
end Oberwolfach
