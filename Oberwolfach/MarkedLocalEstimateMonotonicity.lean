module

public import Oberwolfach.MarkedConfigurationSpokeChanges
public import Oberwolfach.MarkedLocalLoadSpokeChanges

@[expose] public section

/-! Weakening numerical bounds retains the same domains and coefficients. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem markedLocalConfigurations_mono
    (r : ℕ) (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (A : Finset V)
    (bC bP cC cP : ℝ) (hC : cC≤bC) (hP : cP≤bP)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (h : MarkedLocalConfigurationsWithSpokes r P π d A bC bP σ H) :
    MarkedLocalConfigurationsWithSpokes r P π d A cC cP σ H := by
  constructor
  · intro u
    exact (mul_le_mul_of_nonneg_right hC (by positivity)).trans (h.1 u)
  · intro u j v v' hv
    exact (mul_le_mul_of_nonneg_right hP (by positivity)).trans (h.2 u j v v' hv)

theorem markedLocalSpokeLoads_mono
    (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ) (D p k s : ℝ)
    (w : (Fin (m+1)→V)→ℝ) (η θ : ℝ) (hη : η≤θ)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (h : MarkedLocalSpokeLoadsWithSpokes P π d m D p k s w η σ H) :
    MarkedLocalSpokeLoadsWithSpokes P π d m D p k s w θ σ H :=
  fun a=>(h a).trans hη

end Oberwolfach
