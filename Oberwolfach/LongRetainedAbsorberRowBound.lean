module

public import Oberwolfach.RetainedMarkedAbsorberRow
public import Oberwolfach.LongAssignedSamplingRecipe

@[expose] public section
/-! The retained absorber row is small by the same start-count test. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_retained_absorber_row_from_starts
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:0<d) (hm:0<m) (θ:ℝ)
    (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (hstarts:∀w,|rawIntervalHubStartCount π d false σ w-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ w false/d|<(n:ℝ)^(3/4:ℝ)/d):
    ∀w,((retainedFinalMarkedAt π d σ t J w).card:ℝ)≤(n:ℝ)/(100*(m:ℝ))+(n:ℝ)^(3/4:ℝ):=by
  intro w
  have hdR:0<(d:ℝ):=by exact_mod_cast hd
  have hmR:0<(m:ℝ):=by exact_mod_cast hm
  have hh:=(abs_lt.mp (hstarts w)).2
  simp only [longAssignedIntervalProbability, Bool.false_eq_true, ↓reduceIte] at hh
  have hh':=(mul_lt_mul_of_pos_right hh hdR)
  have hc:=retained_marked_absorber_row_le_starts π d hd σ t J w
  field_simp at hh' ⊢
  nlinarith
end Oberwolfach
