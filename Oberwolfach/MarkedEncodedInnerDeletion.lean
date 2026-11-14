module

public import Oberwolfach.MarkedHostRawEncoding
public import Oberwolfach.MarkedPhysicalDeletionRestriction

@[expose] public section

/-! The encoded host agrees with the original sampled coordinates on a
fixed protected inner domain, even after a physical deletion. The induced
deletion uses the actual pullback graph, not a new sampling law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z E K Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_encoded_inner_deletion
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (σ:RawMarkedOutcome V U Γ Color) (I:Finset V) (f:W→V) (g:Z→U)
    (hf:∀ w,f w∈I) (DR:SimpleGraph V):
    rawMarkedRestrictPair f g
      (rawMarkedDeleteRims (rawMarkedEncodeHost tail head ktail khead π σ I) DR.edgeFinset)=
    rawMarkedDeleteRims (rawMarkedRestrictPair f g σ) (DR.comap f).edgeFinset := by
  rw [rawMarkedRestrictPair_deleteRims,rawMarkedEncodeHost_restrict tail head ktail khead π σ I f g hf]

end Oberwolfach
