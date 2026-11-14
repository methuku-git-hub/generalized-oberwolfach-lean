module

public import Oberwolfach.OrdinaryInducedRimCutEmbedding
public import Oberwolfach.OrdinaryRawPairRestrictionGeometry
public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! The common ambient rim cut is exactly the local cut needed by correction
on the fixed vortex subtype, using the same raw sample and direction coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_fixed_vortex_rim_cut_transport
    (P:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (σ:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool) (i:ℕ) (α pstar:ℝ)
    (h:OrdinaryInducedRimCutEvent (Q.extendedVertices (i+1))
      (sampledOrientation (rawWheelGraph P σ) coins) α pstar):
    let f:markedVortexVertexType Q i↪V:=(markedVortexVertexEmbedding Q i).toEmbedding;
    let g:=markedVortexHubEmbedding Q i;
    let I:=markedVortexInnerVertices Q i;
    let localRaw:=ordinaryRawRestrictPair f g σ;
    let localCoins:=fun e:Sym2 (markedVortexVertexType Q i)=>coins (Sym2.map f e);
    OrdinaryInducedRimCutEvent I (sampledOrientation (rawWheelGraph (P.comap f) localRaw) localCoins) α pstar:=by
  intro f g I localRaw localCoins
  have hImg:I.image f=Q.extendedVertices (i+1):=(marked_vortex_inner_images Q i).1
  have hcopy:OrdinaryInducedRimCutEvent I (fun x y=>sampledOrientation (rawWheelGraph P σ) coins (f x) (f y)) α pstar:=by
    apply ordinary_induced_rim_cut_embedding f I _ α pstar
    rw [hImg]
    exact h
  have horient:sampledOrientation (rawWheelGraph (P.comap f) localRaw) localCoins=
      (fun x y=>sampledOrientation (rawWheelGraph P σ) coins (f x) (f y)):=by
    funext x y
    simp [sampledOrientation,orientationBit,localCoins,localRaw,f,ordinaryRawRestrictPair_rim]
  rw [horient]
  exact hcopy
end Oberwolfach
