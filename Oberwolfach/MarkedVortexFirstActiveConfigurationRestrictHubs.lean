module

public import Oberwolfach.MarkedConfigurationsRestrictHubs
public import Oberwolfach.MarkedVortexNonDeeperInnerHubs
public import Oberwolfach.MarkedActualNextActiveAllParentHubsConfigurationEvent

@[expose] public section
/-! The selected first-active configuration estimate is available on all
parent hubs. Restrict it to the nondeeper hubs without changing the sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_vortex_first_active_configuration_restrict_hubs
    {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)
    (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d r:ℕ) (bc bp:ℝ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop):
    let f:=markedVortexActiveVertexEmbedding Q 1
    let g:=markedVortexHubEmbedding Q 0
    let g':=markedVortexNonDeeperHubToPhysical Q 0
    let ρ:=markedVortexActivePermutation Q π hπ 1;
    MarkedLocalConfigurationsWithSpokes r (G.comap f) ρ d Finset.univ bc bp
      (rawMarkedRestrictPair f g σ) (fun b x u=>H b (f x) (g u)) →
    MarkedLocalConfigurationsWithSpokes r (G.comap f) ρ d Finset.univ bc bp
      (rawMarkedRestrictPair f g' σ) (fun b x u=>H b (f x) (g' u)) := by
  intro f g g' ρ h
  apply marked_local_configurations_restrict_hubs r d (G.comap f) ρ Finset.univ bc bp bc bp
    (le_refl _) (le_refl _) _ _ _ (markedVortexNonDeeperHubToParent Q 0) ?_ h
  intro e
  rfl
end Oberwolfach
