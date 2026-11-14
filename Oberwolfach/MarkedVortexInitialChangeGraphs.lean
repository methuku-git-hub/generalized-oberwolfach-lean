module

public import Oberwolfach.MarkedVortexSameSampleChangeGraphs
public import Oberwolfach.MarkedVortexLevelZeroEquivalences

@[expose] public section
/-! At level zero the physical edit bounds have the original scale, because
both level-zero ground sets are the full physical sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_vortex_initial_change_graphs
    {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)
    (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)) (ζ:ℝ)
    (hR:∀a,¬(rawMarkedPairRims G π d σ a↔rawMarkedPairRims G π d τ a)→markedPairPhysical π a∈FR.edgeFinset)
    (hS:∀b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hFR:∀v,(FR.degree v:ℝ)≤ζ*Fintype.card V) (hFS:∀z,(FS.degree z:ℝ)≤ζ*Fintype.card V):
    let f:=markedVortexVertexEmbedding Q 0
    let g:=markedVortexHubEmbedding Q 0
    let ρ:=markedVortexPermutation Q π hπ 0;
    (∀a,¬(rawMarkedPairRims (G.comap f) ρ d (rawMarkedRestrictPair f g σ) a↔
      rawMarkedPairRims (G.comap f) ρ d (rawMarkedRestrictPair f g τ) a)→
      markedPairPhysical ρ a∈(FR.comap f).edgeFinset) ∧
    (∀b v u,¬(H b (f v) (g u)↔H' b (f v) (g u))→
      (FS.comap (Sum.map f g)).Adj (Sum.inl v) (Sum.inr u)) ∧
    (∀v,((FR.comap f).degree v:ℝ)≤ζ*Fintype.card (markedVortexVertexType Q 0)) ∧
    (∀z,((FS.comap (Sum.map f g)).degree z:ℝ)≤ζ*Fintype.card (markedVortexVertexType Q 0)):=by
  have hc:Fintype.card (markedVortexVertexType Q 0)=Fintype.card V:=
    (marked_vortex_level_zero_physical_maps Q π hπ).2.2.2.1
  have hsize:∀i≤0,ζ*Fintype.card V≤(fun _:ℕ=>ζ) i*Fintype.card (markedVortexVertexType Q i):=by
    intro i hi
    have hz:i=0:=by omega
    subst i
    simpa only [hc] using (le_rfl : ζ*Fintype.card V≤ζ*Fintype.card V)
  exact marked_vortex_same_sample_change_graphs Q π hπ d 0 σ τ H H' FR FS
    (ζ*Fintype.card V) (ζ*Fintype.card V) (fun _=>ζ) hR hS hFR hFS hsize hsize 0 le_rfl
end Oberwolfach
