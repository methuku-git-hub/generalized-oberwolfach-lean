module

public import Oberwolfach.OrdinaryRawIntervalGeometry

@[expose] public section

/-! Deleting conflict edges changes no candidate-wheel test, since the
fixed candidate family consists of conflict-independent cycles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {P F : SimpleGraph V} {Hbase : V → U → Prop} {r : ℕ}

theorem ordinaryWheelResources_conflict_free (W : OrdinaryWheel P F Hbase r)
    (e : Sym2 V) (he : Sum.inl e∈ordinaryWheelResources W) : e∉F.edgeSet := by
  induction e using Sym2.ind with
  | _ x y=>
    have hxy := (ordinaryWheelResources_rim W s(x,y)).mp he
    exact W.property.2 x hxy.mem_support_left y hxy.mem_support_right

theorem ordinaryPotentialLoad_delete_conflicts
    (w : OrdinaryWheel P F Hbase r → ℝ) (root : Sym2 V⊕(V×U))
    (Q : SimpleGraph V) (H : V → U → Prop) :
    ordinaryPotentialLoad w root (Q\F) H=ordinaryPotentialLoad w root Q H := by
  unfold ordinaryPotentialLoad
  apply Finset.sum_congr rfl
  intro W _
  congr 1
  unfold patternValue
  apply Finset.prod_congr rfl
  intro e he
  have heW := (Finset.mem_sdiff.mp he).1
  cases e with
  | inl a=>
    have ha := ordinaryWheelResources_conflict_free W a heW
    simp only [ordinaryResourceState,Sum.elim_inl,SimpleGraph.edgeSet_sdiff,
      Set.mem_sdiff,ha,not_false_eq_true,and_true]
    simp only [decide_eq_true_eq]
  | inr a=>rfl

end Oberwolfach
