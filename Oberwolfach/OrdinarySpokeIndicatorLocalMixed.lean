module

public import Oberwolfach.OrdinarySpokePotentialIdentity
public import Oberwolfach.MixedIteAnd

@[expose] public section
/-! A sum over ordinary wheels with a selected hub is the local cycle potential. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 10000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [decU:DecidableEq U] {r:ℕ}
theorem ordinary_spoke_indicator_sum_eq_local_mixed (P Q F:SimpleGraph V) (H:V→U→Prop)
    (weight:OrdinaryCycle P r→ℝ) (D:ℝ) (v:V) (u:U):
    (∑ W:OrdinaryWheel P F (fun _ :V=>fun _ :U=>True) r,
      if W.val.2=u ∧ v∈(W.val.1.val.val).support ∧ W.val.1.val.val≤Q ∧
        (∀ z∈(W.val.1.val.val).support,z≠v→H z u) then weight W.val.1/D else 0)=
      ordinaryLocalPotential P Q F (Finset.univ.filter (fun z=>H z u)) (fun C=>weight C/D) v := by
  let f:=fun (C:OrdinaryCycle P r) (a:U)=>
    if a=u then
      if v∈C.val.val.support ∧ C.val.val≤Q ∧ (∀ z∈C.val.val.support,z≠v→H z u)
        then weight C/D else 0
    else 0
  have heq:(∑ W:OrdinaryWheel P F (fun _ :V=>fun _ :U=>True) r,
      if W.val.2=u ∧ v∈(W.val.1.val.val).support ∧ W.val.1.val.val≤Q ∧
        (∀ z∈(W.val.1.val.val).support,z≠v→H z u) then weight W.val.1/D else 0)=
      ∑ W:OrdinaryWheel P F (fun _ :V=>fun _ :U=>True) r, f W.val.1 W.val.2:=by
    apply Finset.sum_congr rfl
    intro W _
    dsimp only [f]
    exact mixed_ite_and (W.val.2=u)
      (v∈(W.val.1.val.val).support ∧ W.val.1.val.val≤Q ∧
        ∀ z∈(W.val.1.val.val).support,z≠v→H z u) (decU W.val.2 u) (weight W.val.1/D) 0
  rw [heq,ordinaryFullHubWheel_sum P F r f]
  unfold ordinaryLocalPotential
  apply Finset.sum_congr rfl
  intro C _
  dsimp only [f]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,Finset.mem_filter,true_and]
  split_ifs <;> simp_all
end Oberwolfach
