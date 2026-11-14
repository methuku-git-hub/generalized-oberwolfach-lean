module

public import Oberwolfach.MarkedOrdinaryArcIndicator

@[expose] public section
/-! Rewrite the ordinary rim incidence as a sum over positions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {m b:ℕ} {π:Equiv.Perm V}

theorem marked_ordinary_arc_weighted_sum
    (w:MarkedCycleTuple (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b→ℝ) (x z:V):
    (∑ C,if CanonicalMarkedArcMem C (Sum.inl (x,z)) then w C else 0)=
      ∑ i:Fin m,∑ C,if C.val i.castSucc=x ∧ C.val i.succ=z then w C else 0 :=by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C _
  have h:=congrArg (fun a:ℝ=>w C*a) (marked_ordinary_arc_indicator C x z)
  simp only [Finset.mul_sum,mul_ite,mul_one,mul_zero] at h
  exact h
end Oberwolfach
