module

public import Oberwolfach.OrdinaryProtectedPairLocalReference

@[expose] public section
/-! The original preparation assumption that the edited target agrees with
    the sample on the protected pair supplies the local reference condition. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem ordinary_sample_reference_local_containment
    (Target Sample Reference:SimpleGraph V) (Inner:Finset V)
    (hRef:Reference≤Sample)
    (hAgreement:∀v∈Inner,∀w∈Inner,(Target.Adj v w↔Sample.Adj v w)):
    ∀v∈Inner,∀w∈Inner,Reference.Adj v w→Target.Adj v w:=by
  intro v hv w hw hr
  exact (hAgreement v hv w hw).mpr (hRef hr)
end Oberwolfach
