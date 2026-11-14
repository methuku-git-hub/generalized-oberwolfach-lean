module

public import Oberwolfach.GraphCuts
public import Mathlib.Tactic

@[expose] public section

/-! The actual ordered pairs supplied by a forbidden simple graph.
Both directions are retained explicitly; their incidence costs a factor two. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type*} [Fintype V] [DecidableEq V]

def forbiddenGraphPairs (F:SimpleGraph V) (Y:Finset V):Finset (V×V):=
  (Y×ˢY).filter (fun e=>F.Adj e.1 e.2)

theorem forbiddenGraphPairs_distinct (F:SimpleGraph V) (Y:Finset V):
    ∀ e∈forbiddenGraphPairs F Y,e.1≠e.2:=by
  intro e he
  exact F.ne_of_adj (Finset.mem_filter.mp he).2

theorem forbiddenGraphPairs_card (F:SimpleGraph V) (Y:Finset V) (d:ℝ)
    (hd:∀ v,(F.degree v:ℝ)≤d):
    ((forbiddenGraphPairs F Y).card:ℝ)≤Y.card*d:=by
  have he:(forbiddenGraphPairs F Y).card=∑ v∈Y,(Y.filter (fun u=>F.Adj v u)).card:=by
    simp only [forbiddenGraphPairs,Finset.card_filter,Finset.sum_product]
  rw [he,Nat.cast_sum]
  calc
    _≤∑ _v∈Y,d:=by
      apply Finset.sum_le_sum
      intro v _
      have hs:Y.filter (fun u=>F.Adj v u)⊆F.neighborFinset v:=by
        intro u hu;exact (SimpleGraph.mem_neighborFinset _ _ _).mpr (Finset.mem_filter.mp hu).2
      exact (Nat.cast_le.mpr (Finset.card_le_card hs)).trans (by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hd v)
    _=_:=by simp

theorem forbiddenGraphPairs_incidence (F:SimpleGraph V) (Y:Finset V) (v:V):
    ((forbiddenGraphPairs F Y).filter (fun e=>v=e.1 ∨ v=e.2)).card≤2*F.degree v:=by
  have hs:(forbiddenGraphPairs F Y).filter (fun e=>v=e.1 ∨ v=e.2)⊆
      ({v}×ˢF.neighborFinset v)∪(F.neighborFinset v×ˢ{v}):=by
    intro e he
    obtain ⟨he,hv⟩:=Finset.mem_filter.mp he
    have hadj:=(Finset.mem_filter.mp he).2
    rcases hv with hv|hv
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr
        ⟨Finset.mem_singleton.mpr hv.symm,(SimpleGraph.mem_neighborFinset _ _ _).mpr (hv ▸ hadj)⟩)
    · exact Finset.mem_union_right _ (Finset.mem_product.mpr
        ⟨(SimpleGraph.mem_neighborFinset _ _ _).mpr (hv ▸ hadj.symm),Finset.mem_singleton.mpr hv.symm⟩)
  apply (Finset.card_le_card hs).trans
  have hh:=Finset.card_union_le ({v}×ˢF.neighborFinset v) (F.neighborFinset v×ˢ{v})
  simpa only [Finset.card_product,Finset.card_singleton,one_mul,mul_one,
    SimpleGraph.card_neighborFinset_eq_degree,two_mul] using hh

theorem forbiddenGraphPairs_avoidance (F:SimpleGraph V) (Y Z:Finset V) (hZY:Z⊆Y)
    (havoid:∀ e∈forbiddenGraphPairs F Y,¬(e.1∈Z ∧ e.2∈Z)):
    ∀ x∈Z,∀ y∈Z,¬F.Adj x y:=by
  intro x hx y hy hxy
  exact havoid (x,y) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hZY hx,hZY hy⟩,hxy⟩) ⟨hx,hy⟩

end Oberwolfach
