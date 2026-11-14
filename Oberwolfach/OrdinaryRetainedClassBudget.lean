module

public import Oberwolfach.OrdinaryClassFailureBudget
public import Oberwolfach.MixedClassOrdinaryRetentionProjection

@[expose] public section
/-! Turn the ordinary same-sample input bound into the error budget used by
the common retained-class event, without adding or resampling any variables. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_same_sample_retained_class_budget
    {V U:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (a:Bool) (χ:ℝ) (hχ:0≤χ)
    (μ:FiniteLaw (RawWheelOutcome V U Bool Bool)) (E:RawWheelOutcome V U Bool Bool→Prop)
    (hprob:1-(1/(Fintype.card V:ℝ)+3/(Fintype.card V:ℝ)^2)≤μ.probability E):
    letI : ∀ ω:RawWheelOutcome V U Bool Bool,Fintype (mixedClassRetentionSpace false π d a ω):=
      fun ω=>mixedClassRetentionFintype false π d a ω;
    letI : Fintype (Σ ω:RawWheelOutcome V U Bool Bool,mixedClassRetentionSpace false π d a ω):=
      @Sigma.instFintype _ _ (fun ω=>mixedClassRetentionFintype false π d a ω) inferInstance;
    1-(100*χ+200/(Fintype.card V:ℝ))≤
      (μ.sigma (mixedClassActualRetention false π d a)).probability (fun z=>E z.1) := by
  rw [mixed_class_ordinary_retention_projection π d a μ E]
  have hn:1≤Fintype.card V:=Fintype.card_pos
  have hb:=ordinary_combined_failure_below_class_budget (Fintype.card V) hn χ hχ
  linarith
end Oberwolfach
