module

public import Oberwolfach.MarkedLocalConfigurationHubRestriction

@[expose] public section
/-! The active-vertex configuration field follows from an estimate for every
parent hub, after restricting the hub domain and weakening both coefficients. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Z Γ Color:Type} [Fintype V] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U] [DecidableEq Z]

theorem marked_external_hub_configuration_record_input
    (r:ℕ) (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (bC bP β:ℝ) (hC:3*β≤bC) (hP:3*β≤bP)
    (σ:RawMarkedOutcome V U Γ Color) (τ:RawMarkedOutcome V Z Γ Color)
    (g:Z→U) (H:Bool→V→U→Prop)
    (hrim:∀ e,τ (Sum.inl e)=σ (Sum.inl e))
    (hc:MarkedLocalConfigurationsWithSpokes r P π d Finset.univ bC bP σ H):
    MarkedLocalConfigurationsWithSpokes r P π d Finset.univ (3*β) (3*β) τ (fun b x u=>H b x (g u)):=by
  have h:=marked_local_configurations_hub_restriction r P π d Finset.univ bC bP σ τ g H hrim hc
  exact markedLocalConfigurations_mono r P π d Finset.univ bC bP (3*β) (3*β) hC hP τ _ h
end Oberwolfach
