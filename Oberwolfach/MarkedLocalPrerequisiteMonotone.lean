module

public import Oberwolfach.MarkedLocalLoadSpokeChanges
public import Oberwolfach.MarkedConfigurationSpokeChanges

@[expose] public section
/-! Relax local configuration lower bounds and weighted-load error bounds
without changing their fixed domains, weights, or sampled outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
omit [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U] in
theorem marked_local_configurations_with_spokes_mono
    (r:ℕ) (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (A:Finset V)
    (βC βP βC' βP':ℝ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hC:βC'≤βC) (hP:βP'≤βP):
    MarkedLocalConfigurationsWithSpokes r P π d A βC βP σ H→
      MarkedLocalConfigurationsWithSpokes r P π d A βC' βP' σ H:=by
  intro hh
  constructor
  · intro u
    exact (mul_le_mul_of_nonneg_right hC (pow_nonneg (Nat.cast_nonneg _) _)).trans (hh.1 u)
  · intro u j v v' hv
    exact (mul_le_mul_of_nonneg_right hP (pow_nonneg (Nat.cast_nonneg _) _)).trans (hh.2 u j v v' hv)

omit [Fintype Γ] [Fintype Color] in
theorem marked_local_spoke_loads_tolerance_mono
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (D p k s₀:ℝ)
    (weight:(Fin (m+1)→V)→ℝ) (ε ε':ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop) (hle:ε≤ε'):
    MarkedLocalSpokeLoadsWithSpokes P π d m D p k s₀ weight ε σ H→
      MarkedLocalSpokeLoadsWithSpokes P π d m D p k s₀ weight ε' σ H:=by
  intro hh a
  exact (hh a).trans hle
end Oberwolfach
