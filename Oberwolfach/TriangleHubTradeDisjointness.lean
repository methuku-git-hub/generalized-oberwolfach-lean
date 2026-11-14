module

public import Oberwolfach.TriangleTransformerNearCompleteTrades

@[expose] public section
/-! Disjoint vertex domains give edge-disjoint physical rim graphs for
the wheel trades chosen at different hubs. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_hub_trade_rims_disjoint {V J:Type} [Fintype V] [DecidableEq V]
    (A Z:J→Finset V) (R:J→SimpleGraph V)
    (hS:∀ i v w,(R i).Adj v w→v∈A i∪Z i ∧ w∈A i∪Z i)
    (hpair:∀ i j,i≠j→Disjoint (A i∪Z i) (A j∪Z j)):
    ∀ i j,i≠j→Disjoint (R i) (R j):=by
  intro i j hij
  apply disjoint_iff_inf_le.mpr
  intro v w hvw
  exact Finset.disjoint_left.mp (hpair i j hij) (hS i v w hvw.1).1 (hS j v w hvw.2).1
theorem triangle_hub_trade_spokes_disjoint {V U J:Type} [DecidableEq V]
    (A Z:J→Finset V) (u u':J→U)
    (hpair:∀ i j,i≠j→Disjoint (A i∪Z i) (A j∪Z j)):
    let Sp:J→V→U→Prop:=fun i v z=>(v∈A i∪Z i∧z=u i)∨(v∈A i∧z=u' i)
    let Sm:J→V→U→Prop:=fun i v z=>(v∈A i∪Z i∧z=u' i)∨(v∈A i∧z=u i)
    ∀ i j,i≠j→∀ v z,¬(Sp i v z∧Sp j v z) ∧ ¬(Sm i v z∧Sm j v z):=by
  intro Sp Sm i j hij v z
  have hv (i:J) (h:Sp i v z∨Sm i v z):v∈A i∪Z i:=by
    rcases h with h|h <;> rcases h with h|h
    · exact h.1
    · exact Finset.mem_union_left _ h.1
    · exact h.1
    · exact Finset.mem_union_left _ h.1
  exact ⟨fun h=>Finset.disjoint_left.mp (hpair i j hij) (hv i (Or.inl h.1)) (hv j (Or.inl h.2)),
    fun h=>Finset.disjoint_left.mp (hpair i j hij) (hv i (Or.inr h.1)) (hv j (Or.inr h.2))⟩
end Oberwolfach
