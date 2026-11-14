module

public import Oberwolfach.LongAssignedSeedFunctions
public import Oberwolfach.LongAssignedSeedTargets

@[expose] public section
/-! A discarded frequency has zero fixed seed weight at that hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_ordinary_seed_zero_at_discarded_hub
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (m d:ℕ) (θ D:ℝ)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (ni:Fin K→ℕ) (hni:∀i,1≤ni i)
    (w:∀i,OrdinaryCycle P (ni i+2)→ℝ) (i:Fin K)
    (W:OrderedOrdinaryWheel (U:=U) π (3*d) (ni i+2))
    (hzero:longAssignedKeptFraction F hF K θ i W.2=0):
    longAssignedOrdinarySeed F hF K m d θ D P π ni hni w i W=0 :=by
  have hc:longAssignedKeptOrdinaryContribution F hF K θ i W.2=0:=by
    rw [long_assigned_kept_fraction_contribution,hzero]
    ring
  simp only [longAssignedOrdinarySeed,hc,zero_div,zero_mul]
end Oberwolfach
