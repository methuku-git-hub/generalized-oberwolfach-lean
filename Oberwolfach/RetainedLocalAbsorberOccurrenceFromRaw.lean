module

public import Oberwolfach.RetainedMarkedAbsorberOccurrenceOn
public import Oberwolfach.RawIntervalExtendedHubsUpperOn

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_local_absorber_occurrence_from_raw
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (I:Type) (T:Finset I) (A:I→Finset (Fin n)) (H:I→Finset U) (M:ℝ)
    (hraw:∀i∈T,∀v∈A i,((rawIntervalExtendedAnyHubSet π d σ v ∩ H i).card:ℝ) ≤
      4*((H i).card:ℝ)/M+4*((A i).card:ℝ)^(3/4:ℝ)):
    ∀i∈T,∀v∈A i,(((H i).filter (fun w=>v∈retainedFinalMarkedAt π d σ t J w)).card:ℝ) ≤
      4*((H i).card:ℝ)/M+4*((A i).card:ℝ)^(3/4:ℝ):=by
  intro i hi v hv
  have hh:=retained_marked_absorber_occurrence_on_le_extended π d σ (H i) t J v
  exact (by exact_mod_cast hh : (((H i).filter (fun w=>v∈retainedFinalMarkedAt π d σ t J w)).card:ℝ) ≤
    ((rawIntervalExtendedAnyHubSet π d σ v ∩ H i).card:ℝ)).trans (hraw i hi v hv)
end Oberwolfach
