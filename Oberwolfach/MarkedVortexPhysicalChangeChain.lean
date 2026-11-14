module

public import Oberwolfach.MarkedVortexSameSampleChangeGraphs
public import Oberwolfach.MarkedVortexChangeGraphNesting

@[expose] public section
/-! A coherent chain of physical edit graphs for the same ambient
sample and corrected host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

structure MarkedVortexPhysicalChangeChain
    {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)
    (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d L:ℕ) (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (scale:ℕ→ℝ) where
  rim:∀i,SimpleGraph (markedVortexVertexType Q i)
  spoke:∀i,SimpleGraph (markedVortexVertexType Q i⊕markedVortexHubType Q i)
  rimChange:∀i, i≤L→∀a,
    ¬(rawMarkedPairRims (G.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) d
        (rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ) a↔
      rawMarkedPairRims (G.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) d
        (rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) τ) a)→
    markedPairPhysical (markedVortexPermutation Q π hπ i) a∈(rim i).edgeFinset
  spokeChange:∀i,i≤L→∀b v u,
    ¬(H b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u)↔
      H' b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u))→
    (spoke i).Adj (Sum.inl v) (Sum.inr u)
  rimDegree:∀i,i≤L→∀v,((rim i).degree v:ℝ)≤scale i*Fintype.card (markedVortexVertexType Q i)
  spokeDegree:∀i,i≤L→∀z,((spoke i).degree z:ℝ)≤scale i*Fintype.card (markedVortexVertexType Q i)
  rimNested:∀i j (hij:i≤j),rim j=(rim i).comap (markedVortexNestedVertex Q i j hij)
  spokeNested:∀i j (hij:i≤j),spoke j=(spoke i).comap
    (Sum.map (markedVortexNestedVertex Q i j hij) (markedVortexNestedHub Q i j hij))

noncomputable def marked_vortex_physical_change_chain
    {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)
    (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d L:ℕ) (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)) (δR δS:ℝ) (scale:ℕ→ℝ)
    (hR:∀a,¬(rawMarkedPairRims G π d σ a↔rawMarkedPairRims G π d τ a)→markedPairPhysical π a∈FR.edgeFinset)
    (hS:∀b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hFR:∀v,(FR.degree v:ℝ)≤δR) (hFS:∀z,(FS.degree z:ℝ)≤δS)
    (hsizeR:∀i≤L,δR≤scale i*Fintype.card (markedVortexVertexType Q i))
    (hsizeS:∀i≤L,δS≤scale i*Fintype.card (markedVortexVertexType Q i)):
    MarkedVortexPhysicalChangeChain Q π hπ d L σ τ H H' scale:=by
  have hlevels:=marked_vortex_same_sample_change_graphs Q π hπ d L σ τ H H' FR FS δR δS scale
    hR hS hFR hFS hsizeR hsizeS
  refine ⟨(fun i=>FR.comap (markedVortexVertexEmbedding Q i)),
    (fun i=>FS.comap (Sum.map (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i))),?_,?_,?_,?_,?_,?_⟩
  · intro i hi; exact (hlevels i hi).1
  · intro i hi; exact (hlevels i hi).2.1
  · intro i hi; exact (hlevels i hi).2.2.1
  · intro i hi; exact (hlevels i hi).2.2.2
  · intro i j hij;exact (marked_vortex_change_graph_nesting Q FR FS i j hij).1
  · intro i j hij;exact (marked_vortex_change_graph_nesting Q FR FS i j hij).2
end Oberwolfach
