module

public import Oberwolfach.MarkedVortexNestedActiveConfigurationsNondeeperSpokes
public import Oberwolfach.MarkedVortexNestedActiveRowsArbitrarySpokes
public import Oberwolfach.MarkedVortexNestedActiveLoadArbitrarySpokes
public import Oberwolfach.MarkedVortexNonDeeperInnerHubs

@[expose] public section
/-! Put the corrected first active fields into the nested representation
required by the initial parent record. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_vortex_initial_active_fields_to_nested
    {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)
    (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (r d:ℕ) (p k s₀ t η βrec Dload:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weight:(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1)))→ℝ)
    (τ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop):
    let W:=↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1))
    let f:=markedVortexActiveVertexEmbedding Q 1
    let g:=markedVortexNonDeeperHubToPhysical Q 0
    let ρ:=markedVortexActivePermutation Q π hπ 1
    let τloc:=rawMarkedRestrictPair f g τ
    let Hloc:=fun b x u=>H b (f x) (g u);
    MarkedLocalConfigurationsWithSpokes r (G.comap f) ρ d Finset.univ (3*βrec) (3*βrec) τloc Hloc→
    MarkedRowsWithSpokes (G.comap f) ρ d 1 Finset.univ p k (fun u=>q (g u)) (fun u=>s (g u)) a j ((t/8)*Fintype.card W) τloc Hloc→
    MarkedLocalSpokeLoadsWithSpokes (G.comap f) ρ d (r+4) Dload p k s₀ weight (η/4) τloc Hloc→
    let fP:=markedVortexVertexEmbedding Q 0
    let gP:=markedVortexHubEmbedding Q 0
    let fA:=markedVortexNonDeeperVertexEmbedding Q 0
    let fnext:=markedVortexNextActiveInNonDeeper Q 0
    let gA:=markedVortexNonDeeperHubToParent Q 0
    let τP:=rawMarkedRestrictPair fP gP τ
    let HP:=fun b x u=>H b (fP x) (gP u);
    MarkedLocalConfigurationsWithSpokes r ((G.comap fP).comap (fun x=>fA (fnext x))) ρ d Finset.univ
      (3*βrec) (3*βrec) (rawMarkedRestrictPair (fun x=>fA (fnext x)) gA τP) (fun b x u=>HP b (fA (fnext x)) (gA u)) ∧
    MarkedRowsWithSpokes ((G.comap fP).comap (fun x=>fA (fnext x))) ρ d 1 Finset.univ p k (fun u=>q (gP (gA u))) (fun u=>s (gP (gA u))) a j
      ((t/8)*Fintype.card W) (rawMarkedRestrictPair (fun x=>fA (fnext x)) gA τP) (fun b x u=>HP b (fA (fnext x)) (gA u)) ∧
    MarkedLocalSpokeLoadsWithSpokes ((G.comap fP).comap (fun x=>fA (fnext x))) ρ d (r+4) Dload p k s₀ weight (η/4)
      (rawMarkedRestrictPair (fun x=>fA (fnext x)) gA τP) (fun b x u=>HP b (fA (fnext x)) (gA u)) := by
  intro W f g ρ τloc Hloc hcfg hrows hload fP gP fA fnext gA τP HP
  have hc:=marked_vortex_nested_active_configurations_nondeeper_spokes Q π hπ 0 d r (3*βrec) (3*βrec) βrec (le_refl _) (le_refl _) a j τ H hcfg
  have hr:=marked_vortex_nested_active_rows_arbitrary_spokes Q π hπ 0 d p k t (t/8) (le_refl _) q s a j τ H hrows
  have hl:=marked_vortex_nested_active_load_arbitrary_spokes Q π hπ 0 d (r+4) Dload p k s₀ (η/4) (η/4) (le_refl _) a j weight τ H hload
  exact ⟨hc,hr,hl⟩
end Oberwolfach
