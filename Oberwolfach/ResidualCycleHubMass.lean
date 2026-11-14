module

public import Oberwolfach.ResidualActualCycleMass
public import Oberwolfach.AssignedHubSumAgreement

@[expose] public section
/-! Match the actual residual cycle mass to the ordinary matching's hub
assignment, without changing the selected components. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_residual_cycle_mass_by_matching_hub
    {V K A U:Type} [Fintype V] [DecidableEq V] [DecidableEq K]
    [Fintype A] [DecidableEq A] [DecidableEq U]
    {F:SimpleGraph V} (hub₁ hub₂:A→U) (hhub:∀a,hub₁ a=hub₂ a) (w:U)
    (a:ActualResidualData (K:=K) (J:={x:A // hub₁ x=w}) F)
    (ht:a.t=Finset.univ)
    (hC:a.Cembed=a.t.biUnion (fun j=>(a.C j).support.toFinset))
    (weight:A→ℕ) (hlen:∀j,(a.C j).length=weight j.val):
    a.Cembed.card=∑j:{x:A // hub₂ x=w},weight j.val:=by
  rw [actual_residual_cycle_mass a ht hC]
  calc
    _ = ∑j:{x:A // hub₁ x=w},weight j.val:=by apply Finset.sum_congr rfl;intro j hj;exact hlen j
    _ = _:=assigned_hub_sum_agreement hub₁ hub₂ hhub w weight
end Oberwolfach
