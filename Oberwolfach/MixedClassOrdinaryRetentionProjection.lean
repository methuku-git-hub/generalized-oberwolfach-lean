module

public import Oberwolfach.MixedClassActualRetention
public import Oberwolfach.FiniteLawSigmaProjection

@[expose] public section
/-! The ordinary branch of the mixed experiment adds only a singleton. -/
set_option autoImplicit false
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U]

theorem mixed_class_ordinary_retention_projection
    (π:Equiv.Perm V) (d:ℕ) (a:Bool)
    (μ:FiniteLaw (RawWheelOutcome V U Bool Bool)) (E:RawWheelOutcome V U Bool Bool→Prop):
    letI : ∀ ω:RawWheelOutcome V U Bool Bool,Fintype (mixedClassRetentionSpace false π d a ω):=
      fun ω=>mixedClassRetentionFintype false π d a ω;
    letI : Fintype (Σ ω:RawWheelOutcome V U Bool Bool,mixedClassRetentionSpace false π d a ω):=
      @Sigma.instFintype _ _ (fun ω=>mixedClassRetentionFintype false π d a ω) inferInstance;
    (μ.sigma (mixedClassActualRetention false π d a)).probability (fun z=>E z.1)=μ.probability E:=by
  letI : ∀ ω:RawWheelOutcome V U Bool Bool,Fintype (mixedClassRetentionSpace false π d a ω):=
    fun ω=>mixedClassRetentionFintype false π d a ω
  exact finiteLaw_sigma_first_probability μ _ E
end Oberwolfach
