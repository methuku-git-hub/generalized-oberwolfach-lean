module

public import Oberwolfach.RawMarkedResourceCoordinates
public import Oberwolfach.RetainedRawIntervalCardinality

@[expose] public section
/-! The positive-support event rules out raw interval starts of zero
probability, including inactive ordinary hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_zero_weight_no_starts {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (raw:RawMarkedOutcome V U Bool Bool) (q:U→Bool→ℝ) (g j:Bool) (u:U)
    (hzero:q u g=0)
    (hsupport:∀v,rawMarkedPairSpokes π d raw g j true v u→q u g≠0):
    ∀a,¬rawIntervalColouredStart π d (fun e=>raw (Sum.inr (u,e))) a g :=by
  intro a hstart
  have hcovered:rawIntervalCovered π d (fun e=>raw (Sum.inr (u,e))) a g:=
    ⟨a,hstart,permutationWindow_self π 0 (d-1) a⟩
  have hstate:rawIntervalState π d (fun e=>raw (Sum.inr (u,e))) a=some (Sum.inl g):=
    (rawIntervalState_interval_iff π d _ a g).2 hcovered
  have hsp:rawMarkedPairSpokes π d raw g j true a u:=by
    simpa only [rawMarkedPairSpokes,rawMarkedSpokes,rawIntervalFamilyState] using hstate
  exact hsupport a hsp hzero
end Oberwolfach
