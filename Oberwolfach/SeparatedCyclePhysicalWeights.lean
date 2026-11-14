module

public import Oberwolfach.SeparatedOrderedWeightExtension
public import Oberwolfach.OrdinaryAdmissibleCycleLoads
public import Oberwolfach.OrdinaryRawIntervalGeometry

@[expose] public section
/-! Separated host cycles are precisely host cycles avoiding the permutation
conflict graph on their support. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {P:SimpleGraph V} {π:Equiv.Perm V} {b r:ℕ}

def ordinaryCycleSeparatedGood (π:Equiv.Perm V) (b:ℕ) (C:OrdinaryCycle P r):Prop:=
  ∀ x∈C.val.val.support,∀ y∈C.val.val.support,¬(permutationConflictGraph π b).Adj x y

theorem separated_support_iff_conflict (H:SimpleGraph V) (π:Equiv.Perm V) (b:ℕ):
    (∀ x∈H.support,∀ y∈H.support,x≠y→¬PermutationClose π b x y) ↔
      (∀ x∈H.support,∀ y∈H.support,¬(permutationConflictGraph π b).Adj x y):=by
  constructor
  · intro h x hx y hy ha
    exact h x hx y hy ha.1 ha.2
  · intro h x hx y hy hne hclose
    exact h x hx y hy ⟨hne,hclose⟩

def separatedHostCycleToOrdinary (H:SeparatedHostCycle P π b r):OrdinaryCycle P r:=
  ⟨⟨H.val,H.property.1⟩,H.property.2.1⟩

def separatedHostCycleOrdinaryEquiv:
    SeparatedHostCycle P π b r≃{C:OrdinaryCycle P r // ordinaryCycleSeparatedGood π b C} where
  toFun H:=⟨separatedHostCycleToOrdinary H,(separated_support_iff_conflict H.val π b).mp H.property.2.2⟩
  invFun C:=⟨C.val.val.val,C.val.val.property,C.val.property,(separated_support_iff_conflict C.val.val.val π b).mpr C.property⟩
  left_inv H:=by cases H;rfl
  right_inv C:=by cases C;rfl

theorem separatedHostCycle_sum_physical (F:OrdinaryCycle P r→ℝ):
    (∑ H:SeparatedHostCycle P π b r,F (separatedHostCycleToOrdinary H))=
      ∑ C:OrdinaryCycle P r,if ordinaryCycleSeparatedGood π b C then F C else 0:=by
  let Q:=ordinaryCycleSeparatedGood (P:=P) (r:=r) π b
  letI:DecidablePred Q:=fun C=>Classical.propDecidable (Q C)
  let f:=fun C:OrdinaryCycle P r=>if Q C then F C else 0
  have hz:∀ C,¬Q C→f C=0:=by intro C h;simp [f,h]
  have hh:=finite_sum_restrict_of_zero Q f hz
  calc
    _ = ∑ C:{C:OrdinaryCycle P r // Q C},F C.val:=by
      rw [←Equiv.sum_comp separatedHostCycleOrdinaryEquiv]
      rfl
    _ = ∑ C:{C:OrdinaryCycle P r // Q C},f C.val:=by
      apply Finset.sum_congr rfl
      intro C _
      simp [f,C.property]
    _ = ∑ C:OrdinaryCycle P r,f C:=hh.symm
    _ = _:=by
      apply Finset.sum_congr rfl
      intro C _
      change (if Q C then F C else 0)=_
      split_ifs <;> rfl
end Oberwolfach
