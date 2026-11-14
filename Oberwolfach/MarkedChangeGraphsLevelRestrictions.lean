module

public import Oberwolfach.MarkedPhysicalChangesRestrict
public import Oberwolfach.MarkedActiveDeletionDegrees

@[expose] public section
/-! Restrict the same physical change graphs along every level of a
commuting vortex chain, retaining degree bounds on each level's scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_change_graphs_level_restrictions
    (W Z:ℕ→Type) [∀i,Fintype (W i)] [∀i,Fintype (Z i)] [∀i,LinearOrder (W i)] [∀i,DecidableEq (Z i)]
    (f:∀i,W i↪oV) (g:∀i,Z i↪U) (π:Equiv.Perm V) (ρ:∀i,Equiv.Perm (W i))
    (hcomm:∀i x,f i (ρ i x)=π (f i x))
    (G:SimpleGraph V) (d L:ℕ) (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)) (δR δS:ℝ) (scale:ℕ→ℝ)
    (hR:∀a,¬(rawMarkedPairRims G π d σ a↔rawMarkedPairRims G π d τ a)→markedPairPhysical π a∈FR.edgeFinset)
    (hS:∀b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hFR:∀v,(FR.degree v:ℝ)≤δR) (hFS:∀z,(FS.degree z:ℝ)≤δS)
    (hsizeR:∀i≤L,δR≤scale i*Fintype.card (W i))
    (hsizeS:∀i≤L,δS≤scale i*Fintype.card (W i)):
    ∀i≤L,
      (∀a,¬(rawMarkedPairRims (G.comap (f i)) (ρ i) d (rawMarkedRestrictPair (f i) (g i) σ) a↔
        rawMarkedPairRims (G.comap (f i)) (ρ i) d (rawMarkedRestrictPair (f i) (g i) τ) a)→
        markedPairPhysical (ρ i) a∈(FR.comap (f i)).edgeFinset) ∧
      (∀b v u,¬(H b (f i v) (g i u)↔H' b (f i v) (g i u))→
        (FS.comap (Sum.map (f i) (g i))).Adj (Sum.inl v) (Sum.inr u)) ∧
      (∀v,((FR.comap (f i)).degree v:ℝ)≤scale i*Fintype.card (W i)) ∧
      (∀z,((FS.comap (Sum.map (f i) (g i))).degree z:ℝ)≤scale i*Fintype.card (W i)):=by
  intro i hi
  have hrestrict:=marked_physical_changes_restrict (f i) (g i) π (ρ i) (hcomm i) G d σ τ H H' FR FS hR hS
  refine ⟨hrestrict.1,hrestrict.2,?_,?_⟩
  · intro v
    have hn:=graph_comap_injective_degree_le FR (f i).toEmbedding v
    have hr:((FR.comap (f i)).degree v:ℝ)≤FR.degree (f i v):=by exact_mod_cast hn
    exact (hr.trans (hFR _)).trans (hsizeR i hi)
  · intro z
    have hn:=graph_comap_injective_degree_le FS ((f i).toEmbedding.sumMap (g i)) z
    have hr:((FS.comap (Sum.map (f i) (g i))).degree z:ℝ)≤FS.degree (Sum.map (f i) (g i) z):=by
      exact_mod_cast hn
    exact (hr.trans (hFS _)).trans (hsizeS i hi)
end Oberwolfach
