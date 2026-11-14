module

public import Oberwolfach.MarkedRestrictedSpokeColumnByHub
public import Oberwolfach.MarkedVortexFirstActiveExactRims
public import Oberwolfach.MarkedVortexFirstActiveConfigurationRestrictHubs

@[expose] public section
/-! Construct the first-active change graph from exact inner-hub agreement
and local loss/gain estimates on the first vortex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_initial_active_column_from_hub_local
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
    (H H':Bool→V→U→Prop) (inner:Finset U)
    (hmark:∀x u,H true x u↔H' true x u)
    (loss gain ζ:ℝ) (hloss:0≤loss) (hgain:0≤gain)
    (hexact:∀u∈inner,∀x∈Q.extendedVertices 1,H false x u↔H' false x u)
    (hLoss:∀u∉inner,(((Q.extendedVertices 1).filter (fun x=>H false x u∧¬H' false x u)).card:ℝ)≤loss)
    (hGain:∀u∉inner,(((Q.extendedVertices 1).filter (fun x=>H' false x u∧¬H false x u)).card:ℝ)≤gain):
    let W:=↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1))
    let Z:=markedVortexNonDeeperHubType Q 0
    let f:=markedVortexActiveVertexEmbedding Q 1
    let g:=markedVortexNonDeeperHubToPhysical Q 0
    let HL:=fun b v u=>H b (f v) (g u)
    let HL':=fun b v u=>H' b (f v) (g u)
    let FS:=markedSpokeChangeGraph HL HL';
    loss+gain≤ζ*Fintype.card W→
    (∀b v u,¬(HL b v u↔HL' b v u)→FS.Adj (Sum.inl v) (Sum.inr u)) ∧
    (∀u:Z,(FS.degree (Sum.inr u):ℝ)≤ζ*Fintype.card W) :=by
  intro W Z f g HL HL' FS hscale
  have hf:∀x:W,f x∈Q.extendedVertices 1:=by
    intro x
    exact x.val.property
  have hcol:=marked_restricted_spoke_column_bounds_by_hub f.toEmbedding g (Q.extendedVertices 1) hf inner
    H H' hmark loss gain hloss hgain hexact hLoss hGain
  constructor
  · intro b v u hb
    exact (marked_spoke_change_graph_adj HL HL' v u).mpr ⟨b,hb⟩
  · intro u
    exact (hcol u).trans hscale
end Oberwolfach
