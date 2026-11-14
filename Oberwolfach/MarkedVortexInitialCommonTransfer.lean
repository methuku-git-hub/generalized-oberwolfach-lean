module

public import Oberwolfach.MarkedVortexInitialSampleChangeData
public import Oberwolfach.MarkedCommonFieldsUniformPerturbationBelowCap

@[expose] public section
/-! Transfer the common statistics and row/index fields on the initial
parent using the same global rim and spoke change graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_initial_common_transfer
    (r:ℕ) (κ α ω plo klo:ℝ)
    (hκ:0<κ) (hα:0<α) (hω:0<ω) (hp:0<plo) (hk:0<klo):
    ∃cap:ℝ,0<cap ∧ ∀ζ:ℝ,0≤ζ→ζ≤cap→
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
      (π:Equiv.Perm V) (hπ:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
      (d:ℕ) (σglobal τglobal:RawMarkedOutcome V U Γ Color) (Hglobal Hglobal':Bool→V→U→Prop)
      (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)),
    0<Fintype.card V→ω*Fintype.card V≤(Fintype.card U:ℝ)→
    (∀e,σglobal (Sum.inr e)=τglobal (Sum.inr e))→
    (∀a,¬(rawMarkedPairRims G π d σglobal a↔rawMarkedPairRims G π d τglobal a)→markedPairPhysical π a∈FR.edgeFinset)→
    (∀b v u,¬(Hglobal b v u↔Hglobal' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))→
    (∀v,(FR.degree v:ℝ)≤ζ*Fintype.card V)→(∀z,(FS.degree z:ℝ)≤ζ*Fintype.card V)→
    (∀v u,¬(Hglobal false v u∧Hglobal true v u))→
    let W:=markedVortexVertexType Q 0
    let Z:=markedVortexHubType Q 0
    let f:=markedVortexVertexEmbedding Q 0
    let g:=markedVortexHubEmbedding Q 0
    let ρ:=markedVortexPermutation Q π hπ 0
    let P:=G.comap f
    let σ:=rawMarkedRestrictPair f g σglobal
    let τ:=rawMarkedRestrictPair f g τglobal
    let H:=fun b v u=>Hglobal b (f v) (g u)
    let H':=fun b v u=>Hglobal' b (f v) (g u);
    ∀(a:Γ) (j:Color) (rho t Dload βA:ℝ) (q:Z→Γ→ℝ) (s:Z→Color→ℝ),
    let p:=rho*(r+4:ℝ)*t/2
    let k:=p/(r+4:ℝ);
    plo≤p→klo≤k→
    MarkedReferenceStatistics P ρ d a j Dload (κ/8) (κ/2) (α/8) p k ((r+4:ℝ)*t) t σ→
    MarkedReferenceCutFamilies P ρ d a j (α/8) p k t σ→
    MarkedRowsWithSpokes P ρ d (r+12) Finset.univ p k q s a j ((κ/8)*Fintype.card W) σ H→
    MarkedIndicesWithSpokes ρ d (r+12) Finset.univ q s a j ((κ/8)*Fintype.card W) σ H→
    MarkedCommonConfigurationsWithSpokes r P ρ d βA (κ/8) σ H→
    (∀b v,(∑u,if ¬(rawMarkedPairSpokes ρ d σ a j b v u↔H b v u) then (1:ℝ) else 0)≤(κ/8)*Fintype.card Z)→
    (∀b u,(∑v,if ¬(rawMarkedPairSpokes ρ d σ a j b v u↔H b v u) then (1:ℝ) else 0)≤(κ/8)*Fintype.card W)→
    MarkedReferenceStatistics P ρ d a j Dload (κ/4) κ (α/16) p k ((r+4:ℝ)*t) t τ ∧
    MarkedReferenceCutFamilies P ρ d a j (α/16) p k t τ ∧
    MarkedCommonConfigurationsWithSpokes r P ρ d βA (κ/4) τ H' ∧
    MarkedRowsWithSpokes P ρ d (r+12) Finset.univ p k q s a j ((κ/4)*Fintype.card W) τ H' ∧
    MarkedIndicesWithSpokes ρ d (r+12) Finset.univ q s a j ((κ/4)*Fintype.card W) τ H' ∧
    (∀b v,(∑u,if ¬(rawMarkedPairSpokes ρ d τ a j b v u↔H' b v u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card Z) ∧
    (∀b u,(∑v,if ¬(rawMarkedPairSpokes ρ d τ a j b v u↔H' b v u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card W) := by
  obtain ⟨cap,hcap,htransfer⟩:=marked_common_fields_uniform_perturbation_below_cap r κ α ω plo klo hκ hα hω hp hk
  refine ⟨cap,hcap,?_⟩
  intro ζ hζ hζcap V U Γ Color _ _ _ _ _ _ G D m β ε Q π hπ d σglobal τglobal Hglobal Hglobal' FR FS
    hn hU hinterval hR hS hFR hFS htypes W Z f g ρ P σ τ H H' a j rho t Dload βA q s p k
    hp' hk' hstats hcuts hrows hindices hconfig hOldR hOldC
  have hchanges:=marked_vortex_initial_sample_change_data Q π hπ d σglobal τglobal Hglobal Hglobal' FR FS ζ hinterval hR hS hFR hFS
  have hcardW:Fintype.card W=Fintype.card V:=hchanges.2.2.2.2.2.1
  have hcardZ:Fintype.card Z=Fintype.card U:=hchanges.2.2.2.2.2.2
  have hn':0<Fintype.card W:=by rw [hcardW];exact hn
  have hU':ω*Fintype.card W≤(Fintype.card Z:ℝ):=by rw [hcardW,hcardZ];exact hU
  have hdec:(Subtype.instDecidableEq : DecidableEq W)=(fun a b=>Classical.propDecidable (a=b)):=Subsingleton.elim _ _
  try rw [hdec] at hstats hcuts hrows hindices hconfig hOldR hOldC ⊢
  exact htransfer ζ hζ hζcap W Z Γ Color P ρ d a j rho t Dload βA q s σ τ H H' (FR.comap f) (FS.comap (Sum.map f g))
    hn' hU' hchanges.1 hchanges.2.1 hchanges.2.2.1 hchanges.2.2.2.1 hchanges.2.2.2.2.1
    (by intro v u;exact htypes (f v) (g u)) hp' hk' hstats hcuts hrows hindices hconfig hOldR hOldC
end Oberwolfach
