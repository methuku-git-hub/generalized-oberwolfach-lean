module

public import Oberwolfach.MarkedLocalEstimateMonotonicity

@[expose] public section
/-! A configuration estimate with all parent hubs also controls any fixed
subfamily of those hubs, without changing the rim sample or the vertex domain. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Z Γ Color:Type} [Fintype V] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U] [DecidableEq Z]

theorem marked_local_configurations_hub_restriction
    (r:ℕ) (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (A:Finset V) (βC βP:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (τ:RawMarkedOutcome V Z Γ Color)
    (g:Z→U) (H:Bool→V→U→Prop)
    (hrim:∀ e,τ (Sum.inl e)=σ (Sum.inl e))
    (hc:MarkedLocalConfigurationsWithSpokes r P π d A βC βP σ H):
    MarkedLocalConfigurationsWithSpokes r P π d A βC βP τ (fun b x u=>H b x (g u)):=by
  have heq:(fun e=>τ (Sum.inl e))=(fun e=>σ (Sum.inl e)):=funext hrim
  unfold MarkedLocalConfigurationsWithSpokes MarkedLocalPhysicalCounts at hc ⊢
  rw [heq]
  exact ⟨fun u=>hc.1 (g u),fun u j v v' hv=>hc.2 (g u) j v v' hv⟩
end Oberwolfach
