module

public import Oberwolfach.OrdinaryConflictDeletion
public import Oberwolfach.ResourcePatternConcentration

@[expose] public section
/-! Conflict-edge deletion leaves every fixed candidate-wheel pattern unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {P F:SimpleGraph V} {Hbase:V→U→Prop} {r:ℕ}
theorem ordinary_pattern_load_delete_conflicts
    (w:OrdinaryWheel P F Hbase r→ℝ) (root:Sym2 V⊕(V×U)) (Q:SimpleGraph V) (H:V→U→Prop):
    resourcePatternLoad ordinaryWheelResources w (fun _ _=>true) root (ordinaryResourceState (Q\F) H)=
      resourcePatternLoad ordinaryWheelResources w (fun _ _=>true) root (ordinaryResourceState Q H) := by
  unfold resourcePatternLoad
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
