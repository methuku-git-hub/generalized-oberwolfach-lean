module

public import Oberwolfach.RetainedMarkedAbsorberOccurrence

@[expose] public section
/-! Bound the forbidden-hub sets by the sampled extended-interval event. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_marked_absorber_budget
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (m b:ℝ) (hm:0<m) (hb:0≤b) (hU:Fintype.card U≤n)
    (hM:4/m≤b/2) (hN:4*(n:ℝ)^(3/4:ℝ)≤b*n/2)
    (hOcc:∀v,((rawIntervalExtendedAnyHubSet π d σ v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/m+4*(n:ℝ)^(3/4:ℝ)):
    ∀v,((Finset.univ.filter (fun w=>v∈retainedFinalMarkedAt π d σ t J w)).card:ℝ)≤b*n:=by
  intro v
  have hcard:(Fintype.card U:ℝ)≤n:=by exact_mod_cast hU
  have hscale:4*(Fintype.card U:ℝ)/m≤b*n/2:=by
    have hh:=mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg n)
    have hh':(4/m)*(Fintype.card U:ℝ)≤(4/m)*(n:ℝ):=mul_le_mul_of_nonneg_left hcard (by positivity)
    convert hh'.trans hh using 1 <;> ring
  have hsubset:=retained_marked_absorber_occurrence_le_extended π d σ t J v
  have hsub':(((Finset.univ.filter (fun w=>v∈retainedFinalMarkedAt π d σ t J w)).card:ℝ))≤
      (rawIntervalExtendedAnyHubSet π d σ v).card:=by exact_mod_cast hsubset
  linarith [hOcc v]
end Oberwolfach
