module

public import Oberwolfach.MarkedActiveFieldsAndRowsSharedChanges
public import Oberwolfach.MarkedVortexFirstActiveConfigurationRestrictHubs
public import Oberwolfach.MarkedVortexInitialActiveFieldsToNested

@[expose] public section
/-! Transfer the first active row, configuration and weighted load from one
sample to its physical correction and place them in the parent record. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_initial_active_fields_from_selected_tests
    (r:ℕ) (α tstar kstar ζCfg η B pstar iota:ℝ)
    (hζCfg:0<ζCfg) (hη:0<η) (hB:0≤B) (hpstar:0<pstar) (hi:0 < iota) (htstar:0<tstar):
    ∃cap:ℝ,0<cap ∧ ∀ζ:ℝ,0≤ζ→ζ≤cap→
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    ∀(G:SimpleGraph V) (Dnat mm:ℕ) (β ε:ℝ) (Q:Vortex U G Dnat β ε mm)
      (π:Equiv.Perm V) (hπ:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
      (d:ℕ) (σglobal τglobal:RawMarkedOutcome V U Γ Color) (Hglobal Hglobal':Bool→V→U→Prop)
      (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)),
    (∀e,¬(rawMarkedPairRims G π d σglobal e↔rawMarkedPairRims G π d τglobal e)→markedPairPhysical π e∈FR.edgeFinset)→
    (∀b v u,¬(Hglobal b v u↔Hglobal' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))→
    (∀v,(FR.degree v:ℝ)≤ζ*Fintype.card V)→(∀z,(FS.degree z:ℝ)≤ζ*Fintype.card V)→
    (∀v u,¬(Hglobal false v u∧Hglobal true v u))→
    let W:=↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1))
    let Z:=markedVortexNonDeeperHubType Q 0
    let f:=markedVortexActiveVertexEmbedding Q 1
    let g:=markedVortexNonDeeperHubToPhysical Q 0
    let ρ:=markedVortexActivePermutation Q π hπ 1
    let P:=G.comap f
    let σ:=rawMarkedRestrictPair f g σglobal
    let τ:=rawMarkedRestrictPair f g τglobal
    let H:=fun b v u=>Hglobal b (f v) (g u)
    let H':=fun b v u=>Hglobal' b (f v) (g u);
    ∀(D t τweight A eps βrec p k s₀:ℝ) (weight:(Fin (r+4+1)→W)→ℝ)
      (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color),
    0<Fintype.card W→iota*Fintype.card V≤(Fintype.card W:ℝ)→
    3*βrec≤markedLocalCycleCoefficient r α (tstar/2) kstar-(r+5:ℕ)*ζCfg→
    3*βrec≤markedLocalPathCoefficient r α (tstar/2) kstar-(r+4:ℕ)*ζCfg→
    βrec≤t/4→tstar≤t→eps≤η/8→
    (Fintype.card W:ℝ)/2≤D→D≤2*Fintype.card W→
    pstar≤p→pstar≤k→pstar≤s₀→p≤1→k≤1→s₀≤1→
    SuccessorSequenceWeightConditions P ρ (3*d) D τweight A B weight→
    MarkedRowsWithSpokes P ρ d 1 Finset.univ p k (fun u=>q (g u)) (fun u=>s (g u)) a j ((tstar/16)*Fintype.card W) σ H→
    MarkedLocalConfigurationsWithSpokes r P ρ d Finset.univ
      (markedLocalCycleCoefficient r α (tstar/2) kstar-(r+5:ℕ)*(ζCfg/2))
      (markedLocalPathCoefficient r α (tstar/2) kstar-(r+4:ℕ)*(ζCfg/2))
      (rawMarkedRestrictPair f (markedVortexHubEmbedding Q 0) σglobal)
      (fun b v u=>Hglobal b (f v) (markedVortexHubEmbedding Q 0 u))→
    MarkedLocalSpokeLoadsWithSpokes P ρ d (r+4) D p k s₀ weight eps σ H→
    let fP:=markedVortexVertexEmbedding Q 0
    let gP:=markedVortexHubEmbedding Q 0
    let fA:=markedVortexNonDeeperVertexEmbedding Q 0
    let fnext:=markedVortexNextActiveInNonDeeper Q 0
    let gA:=markedVortexNonDeeperHubToParent Q 0
    let τP:=rawMarkedRestrictPair fP gP τglobal
    let HP:=fun b x u=>Hglobal' b (fP x) (gP u);
    MarkedLocalConfigurationsWithSpokes r ((G.comap fP).comap (fun x=>fA (fnext x))) ρ d Finset.univ
      (3*βrec) (3*βrec) (rawMarkedRestrictPair (fun x=>fA (fnext x)) gA τP) (fun b x u=>HP b (fA (fnext x)) (gA u)) ∧
    MarkedRowsWithSpokes ((G.comap fP).comap (fun x=>fA (fnext x))) ρ d 1 Finset.univ p k (fun u=>q (gP (gA u))) (fun u=>s (gP (gA u))) a j
      ((t/8)*Fintype.card W) (rawMarkedRestrictPair (fun x=>fA (fnext x)) gA τP) (fun b x u=>HP b (fA (fnext x)) (gA u)) ∧
    MarkedLocalSpokeLoadsWithSpokes ((G.comap fP).comap (fun x=>fA (fnext x))) ρ d (r+4) D p k s₀ weight (η/4)
      (rawMarkedRestrictPair (fun x=>fA (fnext x)) gA τP) (fun b x u=>HP b (fA (fnext x)) (gA u)) := by
  obtain ⟨cap,hcap,htransfer⟩:=marked_active_fields_and_rows_shared_physical_changes r α tstar kstar ζCfg η B pstar iota hζCfg hη hB hpstar hi htstar
  refine ⟨cap,hcap,?_⟩
  intro ζ hζ hζcap V U Γ Color _ _ _ _ _ _ _ G Dnat mm β ε Q π hπ d σglobal τglobal Hglobal Hglobal' FR FS hR hS hFR hFS htypes
    W Z f g ρ P σ τ H H' D t τweight A eps βrec p k s₀ weight q s a j hn hsize hcycle hpath hβt htt heps hDlo hDhi hp hk hs hp1 hk1 hs1 hw hrow hcfg hload
    fP gP fA fnext gA τP HP
  have hcomm:∀v,f (ρ v)=π (f v):=marked_vortex_active_permutation_embedding Q π hπ 1
  have hcfg':=marked_vortex_first_active_configuration_restrict_hubs Q π hπ d r
    (markedLocalCycleCoefficient r α (tstar/2) kstar-(r+5:ℕ)*(ζCfg/2))
    (markedLocalPathCoefficient r α (tstar/2) kstar-(r+4:ℕ)*(ζCfg/2)) σglobal Hglobal hcfg
  have h:=htransfer ζ hζ hζcap V U W Z Γ Color f g π ρ hcomm G d D t τweight A eps βrec p k s₀ weight
    (fun u=>q (g u)) (fun u=>s (g u)) a j σglobal τglobal Hglobal Hglobal' FR FS hn hsize hR hS hFR hFS htypes hcycle hpath hβt htt heps hDlo hDhi hp hk hs hp1 hk1 hs1 hw hrow hcfg' hload
  exact marked_vortex_initial_active_fields_to_nested Q π hπ r d p k s₀ t η βrec D q s a j weight τglobal Hglobal' h.1 h.2.2 h.2.1
end Oberwolfach
