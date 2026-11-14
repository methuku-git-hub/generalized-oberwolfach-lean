module

public import Oberwolfach.MarkedVortexNestedActiveConfigurationsInput
public import Oberwolfach.MarkedActualNextActiveAllParentHubsConfigurationEvent
public import Oberwolfach.MarkedVortexNonDeeperGeometry
public import Oberwolfach.MarkedVortexNonDeeperHubEmbedding
public import Oberwolfach.RawMarkedPairNestedRims
public import Oberwolfach.MarkedConfigurationsRestrictHubs

@[expose] public section
/-! Convert the same-sample active configuration estimates into the nested
parent representation, restricting only the hub domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_nested_active_configurations_arbitrary_spokes
    (π:Equiv.Perm V) (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (i d r:ℕ) (bc bp b:ℝ) (hbc:3*b≤bc) (hbp:3*b≤bp)
    (a:Γ) (j:Color) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hconfig:MarkedLocalConfigurationsWithSpokes r
      (G.comap (markedVortexActiveVertexEmbedding Q (i+1)))
      (markedVortexActivePermutation Q π hπ (i+1)) d Finset.univ bc bp
      (rawMarkedRestrictPair (markedVortexActiveVertexEmbedding Q (i+1)) (markedVortexHubEmbedding Q i) σ)
      (fun b x u=>H b
        (markedVortexActiveVertexEmbedding Q (i+1) x) (markedVortexHubEmbedding Q i u))):
    let fP:=markedVortexVertexEmbedding Q i
    let gP:=markedVortexHubEmbedding Q i
    let fA:=markedVortexNonDeeperVertexEmbedding Q i
    let f:=markedVortexNextActiveInNonDeeper Q i
    let gA:markedVortexNonDeeperHubType Q i→markedVortexHubType Q i:=Subtype.val
    let ρ:=markedVortexActivePermutation Q π hπ (i+1)
    let σP:=rawMarkedRestrictPair fP gP σ
    let HP:=fun b x u=>H b (fP x) (gP u);
    MarkedLocalConfigurationsWithSpokes r ((G.comap fP).comap (fun x=>fA (f x))) ρ d Finset.univ
      (3*b) (3*b) (rawMarkedRestrictPair (fun x=>fA (f x)) gA σP)
      (fun b x u=>HP b (fA (f x)) (gA u)):=by
  intro fP gP fA f gA ρ σP HP
  have hrim (e:Sym2 _):
      rawMarkedRestrictPair (fun x=>fA (f x)) gA σP (Sum.inl e)=
      rawMarkedRestrictPair (markedVortexActiveVertexEmbedding Q (i+1)) (markedVortexHubEmbedding Q i) σ (Sum.inl e):=by
    exact rawMarked_pair_nested_rims fP (fun x=>fA (f x)) gP gA σ e
  exact marked_local_configurations_restrict_hubs r d _ ρ Finset.univ bc bp (3*b) (3*b) hbc hbp
    _ _ _ gA hrim hconfig
end Oberwolfach
