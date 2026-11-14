module

public import Oberwolfach.MarkedVortexInitialSampleChangeData
public import Oberwolfach.MarkedDeepFieldsUniformPerturbationBelowCap

@[expose] public section
/-! Transfer initial-parent local configurations and weighted spoke loads
using the same global change graphs as the corrected sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_initial_deep_fields_transfer
    (r:ℕ) (α tstar kstar ζCfg theta B pstar:ℝ)
    (hζCfg:0<ζCfg) (hθ:0<theta) (hB:0≤B) (hpstar:0<pstar):
    ∃cap:ℝ,0<cap ∧ ∀ζ:ℝ,0≤ζ→ζ≤cap→
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
      (π:Equiv.Perm V) (hπ:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
      (d:ℕ) (σglobal τglobal:RawMarkedOutcome V U Γ Color) (Hglobal Hglobal':Bool→V→U→Prop)
      (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)),
    0<Fintype.card V→
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
    ∀(rho t τweight A eps βA:ℝ) (weight:(Fin (r+4+1)→W)→ℝ),
    3*βA≤markedLocalCycleCoefficient r α (tstar/2) kstar-(r+5:ℕ)*ζCfg→
    3*βA≤markedLocalPathCoefficient r α (tstar/2) kstar-(r+4:ℕ)*ζCfg→eps≤theta/8→
    let DRef:=2*Fintype.card Z/rho
    let pRef:=rho*(r+4:ℝ)*t/2
    let kRef:=pRef/(r+4:ℝ)
    let sRef:=(r+4:ℝ)*t;
    (Fintype.card W:ℝ)/2≤DRef→DRef≤2*Fintype.card W→
    pstar≤pRef→pstar≤kRef→pstar≤sRef→pRef≤1→kRef≤1→sRef≤1→
    SuccessorSequenceWeightConditions P ρ (3*d) DRef τweight A B weight→
    MarkedLocalConfigurationsWithSpokes r P ρ d Finset.univ
      (markedLocalCycleCoefficient r α (tstar/2) kstar-(r+5:ℕ)*(ζCfg/2))
      (markedLocalPathCoefficient r α (tstar/2) kstar-(r+4:ℕ)*(ζCfg/2)) σ H→
    MarkedLocalSpokeLoadsWithSpokes P ρ d (r+4) DRef pRef kRef sRef weight eps σ H→
    MarkedLocalConfigurationsWithSpokes r P ρ d Finset.univ
      (3*min βA (t/4)) (3*min βA (t/4)) τ H' ∧
    MarkedLocalSpokeLoadsWithSpokes P ρ d (r+4) DRef pRef kRef sRef weight (theta/4) τ H' := by
  obtain ⟨cap,hcap,htransfer⟩:=marked_deep_fields_uniform_perturbation_below_cap r α tstar kstar ζCfg theta B pstar hζCfg hθ hB hpstar
  refine ⟨cap,hcap,?_⟩
  intro ζ hζ hζcap V U Γ Color _ _ _ _ _ _ G D m β ε Q π hπ d σglobal τglobal Hglobal Hglobal' FR FS
    hn hinterval hR hS hFR hFS htypes W Z f g ρ P σ τ H H' rho t τweight A eps βA weight hcycle hpath heps
    DRef pRef kRef sRef hDlo hDhi hp hk hs hp1 hk1 hs1 hw hcfg hload
  have hchanges:=marked_vortex_initial_sample_change_data Q π hπ d σglobal τglobal Hglobal Hglobal' FR FS ζ hinterval hR hS hFR hFS
  have hcardW:Fintype.card W=Fintype.card V:=hchanges.2.2.2.2.2.1
  have hn':0<Fintype.card W:=by rw [hcardW];exact hn
  have hdec:(Subtype.instDecidableEq : DecidableEq W)=(fun a b=>Classical.propDecidable (a=b)):=Subsingleton.elim _ _
  try rw [hdec] at hw hcfg hload ⊢
  exact htransfer ζ hζ hζcap W Z Γ Color P ρ d rho t τweight A eps βA weight σ τ H H' (FR.comap f) (FS.comap (Sum.map f g))
    hn' hchanges.2.1 hchanges.2.2.1 hchanges.2.2.2.1 hchanges.2.2.2.2.1
    (by intro v u;exact htypes (f v) (g u)) hcycle hpath heps hDlo hDhi hp hk hs hp1 hk1 hs1 hw hcfg hload
end Oberwolfach
