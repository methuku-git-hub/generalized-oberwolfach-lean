module

public import Oberwolfach.MarkedVortexNestedActiveLoadInput
public import Oberwolfach.MarkedActualNextActiveNonDeeperHubsLoadEvent
public import Oberwolfach.MarkedVortexNonDeeperGeometry
public import Oberwolfach.MarkedVortexNonDeeperHubEmbedding
public import Oberwolfach.RawMarkedPairNestedRims
public import Oberwolfach.MarkedLocalSpokeLoadRimEquality
public import Oberwolfach.MarkedLocalEstimateMonotonicity

@[expose] public section
/-! Identify a non-deeper-hub spoke load with the nested sample used by a
parent level record, without changing the root domain or wheel weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_nested_active_load_arbitrary_spokes
    (π:Equiv.Perm V) (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (i d c:ℕ) (Dload p k s₀ err η:ℝ) (herr:err≤η)
    (a:Γ) (j:Color)
    (weight:(Fin (c+1)→↥((Finset.univ\markedVortexInnerVertices Q (i+1)):Finset (markedVortexVertexType Q (i+1))))→ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hload:MarkedLocalSpokeLoadsWithSpokes (G.comap (markedVortexActiveVertexEmbedding Q (i+1)))
      (markedVortexActivePermutation Q π hπ (i+1)) d c Dload p k s₀ weight err
      (rawMarkedRestrictPair (markedVortexActiveVertexEmbedding Q (i+1)) (markedVortexNonDeeperHubToPhysical Q i) σ)
      (fun b x u=>H b
        (markedVortexActiveVertexEmbedding Q (i+1) x) (markedVortexNonDeeperHubToPhysical Q i u))):
    let Z:=markedVortexHubType Q i
    let Zkeep:=markedVortexNonDeeperHubType Q i
    let fP:=markedVortexVertexEmbedding Q i
    let gP:=markedVortexHubEmbedding Q i
    let fA:=markedVortexNonDeeperVertexEmbedding Q i
    let f:=markedVortexNextActiveInNonDeeper Q i
    let gA:Zkeep→Z:=Subtype.val
    let ρ:=markedVortexActivePermutation Q π hπ (i+1)
    let σP:=rawMarkedRestrictPair fP gP σ
    let HP:=fun b x u=>H b (fP x) (gP u);
    MarkedLocalSpokeLoadsWithSpokes ((G.comap fP).comap (fun x=>fA (f x))) ρ d c Dload p k s₀ weight η
      (rawMarkedRestrictPair (fun x=>fA (f x)) gA σP) (fun b x u=>HP b (fA (f x)) (gA u)):=by
  intro Z Zkeep fP gP fA f gA ρ σP HP
  have hrim (e:Sym2 _):
      rawMarkedRestrictPair (fun x=>fA (f x)) gA σP (Sum.inl e)=
      rawMarkedRestrictPair (markedVortexActiveVertexEmbedding Q (i+1)) (markedVortexNonDeeperHubToPhysical Q i) σ (Sum.inl e):=by
    exact rawMarked_pair_nested_rims fP (fun x=>fA (f x)) gP gA σ e
  have he:=marked_local_spoke_loads_rim_equality (G.comap (markedVortexActiveVertexEmbedding Q (i+1))) ρ d c Dload p k s₀ weight err
    (rawMarkedRestrictPair (markedVortexActiveVertexEmbedding Q (i+1)) (markedVortexNonDeeperHubToPhysical Q i) σ)
    (rawMarkedRestrictPair (fun x=>fA (f x)) gA σP)
    (fun b x u=>H b
        (markedVortexActiveVertexEmbedding Q (i+1) x) (markedVortexNonDeeperHubToPhysical Q i u)) hrim hload
  exact markedLocalSpokeLoads_mono (G.comap (markedVortexActiveVertexEmbedding Q (i+1))) ρ d c Dload p k s₀ weight err η herr
    (rawMarkedRestrictPair (fun x=>fA (f x)) gA σP) _ he
end Oberwolfach
