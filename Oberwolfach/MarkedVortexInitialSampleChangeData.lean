module

public import Oberwolfach.MarkedVortexInitialChangeGraphs
public import Oberwolfach.RawMarkedRestrictionIntervalAgreement

@[expose] public section
/-! The original global changes restrict to the initial parent with the
same error scale and unchanged interval coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_vortex_initial_sample_change_data
    {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)
    (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)) (ζ:ℝ)
    (hinterval:∀e,σ (Sum.inr e)=τ (Sum.inr e))
    (hR:∀a,¬(rawMarkedPairRims G π d σ a↔rawMarkedPairRims G π d τ a)→markedPairPhysical π a∈FR.edgeFinset)
    (hS:∀b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hFR:∀v,(FR.degree v:ℝ)≤ζ*Fintype.card V) (hFS:∀z,(FS.degree z:ℝ)≤ζ*Fintype.card V):
    let f:=markedVortexVertexEmbedding Q 0
    let g:=markedVortexHubEmbedding Q 0
    let ρ:=markedVortexPermutation Q π hπ 0
    let σ₀:=rawMarkedRestrictPair f g σ
    let τ₀:=rawMarkedRestrictPair f g τ
    let H₀:=fun b v u=>H b (f v) (g u)
    let H₀':=fun b v u=>H' b (f v) (g u)
    let FR₀:=FR.comap f
    let FS₀:=FS.comap (Sum.map f g);
    (∀e,σ₀ (Sum.inr e)=τ₀ (Sum.inr e)) ∧
    (∀a,¬(rawMarkedPairRims (G.comap f) ρ d σ₀ a↔rawMarkedPairRims (G.comap f) ρ d τ₀ a)→markedPairPhysical ρ a∈FR₀.edgeFinset) ∧
    (∀b v u,¬(H₀ b v u↔H₀' b v u)→FS₀.Adj (Sum.inl v) (Sum.inr u)) ∧
    (∀v,(FR₀.degree v:ℝ)≤ζ*Fintype.card (markedVortexVertexType Q 0)) ∧
    (∀z,(FS₀.degree z:ℝ)≤ζ*Fintype.card (markedVortexVertexType Q 0)) ∧
    Fintype.card (markedVortexVertexType Q 0)=Fintype.card V ∧
    Fintype.card (markedVortexHubType Q 0)=Fintype.card U:=by
  intro f g ρ σ₀ τ₀ H₀ H₀' FR₀ FS₀
  have hh:=marked_vortex_initial_change_graphs Q π hπ d σ τ H H' FR FS ζ hR hS hFR hFS
  exact ⟨raw_marked_restriction_interval_agreement f g σ τ hinterval,hh.1,hh.2.1,hh.2.2.1,hh.2.2.2,
    (marked_vortex_level_zero_physical_maps Q π hπ).2.2.2.1,
    (marked_vortex_level_zero_physical_maps Q π hπ).2.2.2.2⟩
end Oberwolfach
