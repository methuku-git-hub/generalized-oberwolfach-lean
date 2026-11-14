module

public import Oberwolfach.SampledDomainDegreeChanges

@[expose] public section
/-! A changed neighbourhood restricted away from roots differs from the
original intersection by at most the edits plus the removed roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [DecidableEq V]

theorem ordinary_nonroot_intersection_change (A A₀ S T:Finset V) (L:ℝ)
    (hchange:((changed A A₀).card:ℝ)≤L):
    |((A∩(S\T)).card:ℝ)-(A₀∩S).card|≤L+T.card:=by
  have hh:=deleted_intersection_card_change_bound A A₀ S T
  have he:A∩(S\T)=(A∩S)\T:=by ext x;simp [and_assoc]
  rw [he]
  linarith only [hh,hchange]
end Oberwolfach
