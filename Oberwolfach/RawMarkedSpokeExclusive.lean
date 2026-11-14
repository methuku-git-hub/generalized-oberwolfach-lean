module

public import Oberwolfach.RawMarkedResourceCoordinates

@[expose] public section
/-! The marked-interval and ordinary-spoke labels are disjoint states of the
same raw interval variable. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_marked_pair_spoke_exclusive
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (raw:RawMarkedOutcome V U Bool Bool) (v:V) (u:U):
    rawMarkedPairSpokes π d raw true true true v u→¬rawMarkedPairSpokes π d raw true true false v u:=by
  intro ht hf
  change rawIntervalFamilyState π d (fun e=>raw (Sum.inr e)) (v,u)=some (Sum.inl true) at ht
  change rawIntervalFamilyState π d (fun e=>raw (Sum.inr e)) (v,u)=some (Sum.inr true) at hf
  rw [ht] at hf
  cases hf
end Oberwolfach
