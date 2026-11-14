module

public import Oberwolfach.MixedClassConcreteRawViews
public import Oberwolfach.RawMarkedRetention

@[expose] public section
/-! Use the manuscript's start-wise uniform retention for a marked class and
no extra sampling for an ordinary class. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U]

abbrev MixedClassRaw (marked:Bool) := mixedClassState marked
  (∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e)
  (RawWheelOutcome V U Bool Bool)

def mixedClassRetentionSpace (marked:Bool) (π:Equiv.Perm V) (d:ℕ) (a:Bool):
    MixedClassRaw (V:=V) (U:=U) marked→Type:=by
  cases marked with
  | false => exact fun _=>Unit
  | true =>
    intro ω
    let σ:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (ω e)
    let S:=rawStartHubSet π d (fun e=>σ (Sum.inr e)) a
    exact StartRetentionOutcome S (startRetentionMinimum S)

instance mixedClassRetentionFintype (marked:Bool) (π:Equiv.Perm V) (d:ℕ) (a:Bool)
    (ω:MixedClassRaw (V:=V) (U:=U) marked):Fintype (mixedClassRetentionSpace marked π d a ω):=by
  cases marked <;> dsimp [mixedClassRetentionSpace] <;> infer_instance

def mixedClassActualRetention (marked:Bool) (π:Equiv.Perm V) (d:ℕ) (a:Bool)
    (ω:MixedClassRaw (V:=V) (U:=U) marked):FiniteLaw (mixedClassRetentionSpace marked π d a ω):=by
  cases marked with
  | false => exact FiniteLaw.uniform Unit
  | true =>
    let σ:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (ω e)
    let S:=rawStartHubSet π d (fun e=>σ (Sum.inr e)) a
    exact startRetentionLaw S (startRetentionMinimum S) (startRetentionMinimum_le S)
end Oberwolfach
