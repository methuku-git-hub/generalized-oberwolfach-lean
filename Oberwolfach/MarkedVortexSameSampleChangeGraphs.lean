module

public import Oberwolfach.MarkedChangeGraphsLevelRestrictions
public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! The physical edits of the corrected sample restrict along the actual
preselected vortex, using its canonical level maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_vortex_same_sample_change_graphs
    {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)
    (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d L:ℕ) (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)) (δR δS:ℝ) (scale:ℕ→ℝ)
    (hR:∀a,¬(rawMarkedPairRims G π d σ a↔rawMarkedPairRims G π d τ a)→markedPairPhysical π a∈FR.edgeFinset)
    (hS:∀b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hFR:∀v,(FR.degree v:ℝ)≤δR) (hFS:∀z,(FS.degree z:ℝ)≤δS)
    (hsizeR:∀i≤L,δR≤scale i*Fintype.card (markedVortexVertexType Q i))
    (hsizeS:∀i≤L,δS≤scale i*Fintype.card (markedVortexVertexType Q i)):
    ∀i≤L,
      let f:=markedVortexVertexEmbedding Q i
      let g:=markedVortexHubEmbedding Q i
      let ρ:=markedVortexPermutation Q π hπ i;
      (∀a,¬(rawMarkedPairRims (G.comap f) ρ d (rawMarkedRestrictPair f g σ) a↔
        rawMarkedPairRims (G.comap f) ρ d (rawMarkedRestrictPair f g τ) a)→
        markedPairPhysical ρ a∈(FR.comap f).edgeFinset) ∧
      (∀b v u,¬(H b (f v) (g u)↔H' b (f v) (g u))→
        (FS.comap (Sum.map f g)).Adj (Sum.inl v) (Sum.inr u)) ∧
      (∀v,((FR.comap f).degree v:ℝ)≤scale i*Fintype.card (markedVortexVertexType Q i)) ∧
      (∀z,((FS.comap (Sum.map f g)).degree z:ℝ)≤scale i*Fintype.card (markedVortexVertexType Q i)):=by
  exact marked_change_graphs_level_restrictions (markedVortexVertexType Q) (markedVortexHubType Q)
    (markedVortexVertexEmbedding Q) (markedVortexHubEmbedding Q) π (markedVortexPermutation Q π hπ)
    (fun i=>(marked_vortex_permutation_compatibility Q π hπ i).1) G d L σ τ H H' FR FS δR δS scale
    hR hS hFR hFS hsizeR hsizeS
end Oberwolfach
