module

public import Oberwolfach.MarkedConfigurationSpokeChanges

@[expose] public section
/-! Restrict the hub domain of local configuration estimates. No change is
made to the physical rim states or to the vertex domain. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U U' Γ Color:Type} [Fintype V] [LinearOrder V]
  [Fintype U] [Fintype U'] [DecidableEq U] [DecidableEq U']
  [Fintype Γ] [Fintype Color]

theorem marked_local_configurations_restrict_hubs
    (r d:ℕ) (P:SimpleGraph V) (π:Equiv.Perm V) (A:Finset V)
    (βC βP βC' βP':ℝ) (hc:βC'≤βC) (hp:βP'≤βP)
    (σ:RawMarkedOutcome V U Γ Color) (σ':RawMarkedOutcome V U' Γ Color)
    (H':Bool→V→U'→Prop) (g:U→U')
    (hrim:∀ e:Sym2 V,σ (Sum.inl e)=σ' (Sum.inl e))
    (h:MarkedLocalConfigurationsWithSpokes r P π d A βC βP σ' H'):
    MarkedLocalConfigurationsWithSpokes r P π d A βC' βP' σ (fun b x u=>H' b x (g u)):=by
  unfold MarkedLocalConfigurationsWithSpokes MarkedLocalPhysicalCounts at h ⊢
  have hσ:(fun e:Sym2 V=>σ (Sum.inl e))=(fun e:Sym2 V=>σ' (Sum.inl e)):=funext hrim
  rw [hσ]
  constructor
  · intro u
    exact (mul_le_mul_of_nonneg_right hc (pow_nonneg (Nat.cast_nonneg _) _)).trans (h.1 (g u))
  · intro u j v v' hv
    exact (mul_le_mul_of_nonneg_right hp (pow_nonneg (Nat.cast_nonneg _) _)).trans (h.2 (g u) j v v' hv)
end Oberwolfach
