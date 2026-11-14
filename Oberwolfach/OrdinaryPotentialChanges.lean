module

public import Oberwolfach.OrdinaryPairDeletionCosts
public import Oberwolfach.SymmetricPairSums

@[expose] public section

/-! Potential-load changes are bounded by the pair loads of actual changed
physical edges. Parent wheels, coefficients and the omitted root are fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {P F : SimpleGraph V} {Hbase : V → U → Prop} {r : ℕ}

theorem ordinaryPotentialLoad_stability_ordered
    (w : OrdinaryWheel P F Hbase r → ℝ) (hw : ∀ W,0≤w W)
    (root : Sym2 V⊕(V×U)) (Q Q' : SimpleGraph V) (H H' : V → U → Prop) :
    |ordinaryPotentialLoad w root Q' H'-ordinaryPotentialLoad w root Q H|≤
      (∑ x,∑ y,if ¬(Q.Adj x y↔Q'.Adj x y) then ordinaryOmittedPairLoad w root (Sum.inl s(x,y)) else 0)+
      (∑ v,∑ u,if ¬(H v u↔H' v u) then ordinaryOmittedPairLoad w root (Sum.inr (v,u)) else 0) := by
  let D := Finset.univ.filter (fun e=>ordinaryResourceState Q H e≠ordinaryResourceState Q' H' e)
  have hb := ordinaryPotentialLoad_stability w hw root Q Q' H H' D
    (by intro e he;simpa only [D,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using he)
  change |ordinaryPotentialLoad w root Q' H'-ordinaryPotentialLoad w root Q H|≤
    ∑ e∈D,ordinaryOmittedPairLoad w root e at hb
  have he : (∑ e∈D,ordinaryOmittedPairLoad w root e)=
      (∑ e : Sym2 V,if ¬(e∈Q.edgeSet↔e∈Q'.edgeSet) then ordinaryOmittedPairLoad w root (Sum.inl e) else 0)+
      (∑ v,∑ u,if ¬(H v u↔H' v u) then ordinaryOmittedPairLoad w root (Sum.inr (v,u)) else 0) := by
    dsimp only [D]
    rw [Finset.sum_filter,Fintype.sum_sum_type]
    simp only [ordinaryResourceState,Sum.elim_inl,Sum.elim_inr,ne_eq,decide_eq_decide,Fintype.sum_prod_type]
  rw [he] at hb
  apply hb.trans
  refine add_le_add ?_ (le_refl _)
  have hs := sum_sym2_le_ordered
    (fun e=>if ¬(e∈Q.edgeSet↔e∈Q'.edgeSet) then ordinaryOmittedPairLoad w root (Sum.inl e) else 0)
    (fun e=>by
      by_cases h : ¬(e∈Q.edgeSet↔e∈Q'.edgeSet)
      · rw [if_pos h];exact ordinaryOmittedPairLoad_nonneg w hw root _
      · simp only [if_neg h,le_refl])
  have ht : (∑ x,∑ y,if ¬(s(x,y)∈Q.edgeSet↔s(x,y)∈Q'.edgeSet) then ordinaryOmittedPairLoad w root (Sum.inl s(x,y)) else 0)=
      (∑ x,∑ y,if ¬(Q.Adj x y↔Q'.Adj x y) then ordinaryOmittedPairLoad w root (Sum.inl s(x,y)) else 0) := by
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    simp only [SimpleGraph.mem_edgeSet]
  exact hs.trans_eq ht

end Oberwolfach
