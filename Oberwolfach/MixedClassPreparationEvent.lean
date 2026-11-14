module

public import Oberwolfach.MixedClassMarkedRetentionProjection
public import Oberwolfach.MixedClassOrdinaryRetentionProjection

@[expose] public section
/-! Select the marked preparation event or the ordinary event according to
the class, while keeping each branch's original retained law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U]

def mixedClassPreparationEvent (marked:Bool) (π:Equiv.Perm V) (d:ℕ) (a:Bool)
    (Marked:(Σ ω:MixedClassRaw (V:=V) (U:=U) true,mixedClassRetentionSpace true π d a ω)→Prop)
    (Ordinary:RawWheelOutcome V U Bool Bool→Prop):
    (Σ ω:MixedClassRaw (V:=V) (U:=U) marked,mixedClassRetentionSpace marked π d a ω)→Prop:=by
  cases marked with
  | false => exact fun z=>Ordinary z.1
  | true => exact Marked

theorem mixed_class_preparation_probability
    (marked:Bool) (π:Equiv.Perm V) (d:ℕ) (a:Bool) (δ:ℝ)
    (μM:FiniteLaw (MixedClassRaw (V:=V) (U:=U) true))
    (μO:FiniteLaw (RawWheelOutcome V U Bool Bool))
    (Marked:(Σ ω:MixedClassRaw (V:=V) (U:=U) true,mixedClassRetentionSpace true π d a ω)→Prop)
    (Ordinary:RawWheelOutcome V U Bool Bool→Prop)
    (hM:marked=true→1-δ≤(μM.sigma (mixedClassActualRetention true π d a)).probability Marked)
    (hO:marked=false→1-δ≤μO.probability Ordinary):
    let raw:=mixedClassLaw marked μM μO
    letI : ∀ ω:MixedClassRaw (V:=V) (U:=U) marked,Fintype (mixedClassRetentionSpace marked π d a ω):=
      fun ω=>mixedClassRetentionFintype marked π d a ω;
    1-δ≤(raw.sigma (mixedClassActualRetention marked π d a)).probability
      (mixedClassPreparationEvent marked π d a Marked Ordinary):=by
  cases marked with
  | false =>
    intro raw
    have hh:=mixed_class_ordinary_retention_projection π d a μO Ordinary
    change 1-δ≤(μO.sigma (mixedClassActualRetention false π d a)).probability (fun z=>Ordinary z.1)
    rw [hh]
    exact hO rfl
  | true =>
    intro raw
    change 1-δ≤(μM.sigma (mixedClassActualRetention true π d a)).probability Marked
    exact hM rfl
end Oberwolfach
