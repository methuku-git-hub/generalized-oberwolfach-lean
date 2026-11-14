module

public import Oberwolfach.LongClassRequiredCrossingDegree

@[expose] public section
/-! Removing edges entirely inside the protected set leaves a uniformly
bounded-degree required graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]

theorem long_class_required_non_inner_degree
    (P S Sel Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (Req:V→V→Prop) (Pack:Finset (Sym2 V)) (hSP:S≤P):
    let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Kplus:=longClassInnerRequiredRepair S Used K I Pack
    let Koutside:=Kplus\spanningRestriction (⊤:SimpleGraph V) I;
    ∀v,Koutside.degree v≤6*d+2 :=by
  intro K Kplus Koutside v
  by_cases hv:v∈I
  · have hsub:Koutside.neighborFinset v⊆(Kplus.neighborFinset v).filter (fun w=>w∉I):=by
      intro w hw
      have hadj:Koutside.Adj v w:=(SimpleGraph.mem_neighborFinset _ _ _).mp hw
      change Kplus.Adj v w ∧ ¬(spanningRestriction (⊤:SimpleGraph V) I).Adj v w at hadj
      apply Finset.mem_filter.mpr
      refine ⟨(SimpleGraph.mem_neighborFinset _ _ _).mpr hadj.1,?_⟩
      intro hwI
      apply hadj.2
      exact (spanningRestriction_adj _ _ _ _).mpr ⟨hadj.1.ne,hv,hwI⟩
    have hc:=Finset.card_le_card hsub
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at hc
    exact hc.trans (long_class_required_crossing_degree P S Sel Used π d I Req Pack hSP v)
  · have hsub:Koutside.neighborFinset v⊆Kplus.neighborFinset v:=by
      intro w hw
      have hadj:Koutside.Adj v w:=(SimpleGraph.mem_neighborFinset _ _ _).mp hw
      exact (SimpleGraph.mem_neighborFinset _ _ _).mpr hadj.1
    have hc:=Finset.card_le_card hsub
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at hc
    exact hc.trans (long_class_required_outside_degree P S Sel Used π d I Req Pack hSP v hv)
end Oberwolfach
