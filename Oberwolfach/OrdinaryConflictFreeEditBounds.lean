module

public import Oberwolfach.OrdinaryRelationChangeCounts

@[expose] public section
/-! Conflict deletion does not increase the symmetric rim edit when the
actual edited graph already avoids the conflict graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_conflict_free_edit_bounds (Qraw Q F:SimpleGraph V) (H₀ H:V→U→Prop) (d:ℝ)
    (hQF:Disjoint Q F)
    (hR:∀v,((changed (Qraw.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤d)
    (hRow:∀v,((changed (Finset.univ.filter (H₀ v)) (Finset.univ.filter (H v))).card:ℝ)≤d)
    (hCol:∀u,((changed (Finset.univ.filter (fun v=>H₀ v u)) (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤d):
    (∀x,(∑y,bipAdj (fun x y=>¬((Qraw\F).Adj x y↔Q.Adj x y)) x y)≤d) ∧
    (∀x,(∑u,bipAdj (fun x u=>¬(H₀ x u↔H x u)) x u)≤d) ∧
    (∀u,(∑x,bipAdj (fun x u=>¬(H₀ x u↔H x u)) x u)≤d):=by
  have hpoint (x y:V):¬((Qraw\F).Adj x y↔Q.Adj x y)→¬(Qraw.Adj x y↔Q.Adj x y):=by
    intro hchanged heq
    have hnot:Q.Adj x y→¬F.Adj x y:=by
      intro hq hf
      exact (disjoint_iff_inf_le.mp hQF) ⟨hq,hf⟩
    apply hchanged
    simp only [SimpleGraph.sdiff_adj]
    tauto
  constructor
  · intro x
    have hRx:((changed (Finset.univ.filter (Qraw.Adj x)) (Finset.univ.filter (Q.Adj x))).card:ℝ)≤d:=by
      simpa only [SimpleGraph.neighborFinset_eq_filter] using hR x
    have hh:(∑y,if ¬(Qraw.Adj x y↔Q.Adj x y) then (1:ℝ) else 0)≤d:=by
      convert (ordinary_relation_change_sum (Qraw.Adj x) (Q.Adj x)).le.trans hRx using 1 <;>
        congr! 8 <;> exact Subsingleton.elim _ _
    apply (Finset.sum_le_sum (fun y _=>?_)).trans hh
    dsimp only [bipAdj]
    by_cases he:¬((Qraw\F).Adj x y↔Q.Adj x y)
    · have hp:=hpoint x y he
      simp only [if_pos hp]
      split_ifs <;> norm_num
    · simp only [if_neg he]
      split_ifs <;> norm_num
  · constructor
    · intro x
      have hh:=(ordinary_relation_change_sum (H₀ x) (H x)).le.trans (hRow x)
      convert hh using 1 <;> simp only [bipAdj] <;> congr! 8 <;> exact Subsingleton.elim _ _
    · intro u
      have hh:=(ordinary_relation_change_sum (fun x=>H₀ x u) (fun x=>H x u)).le.trans (hCol u)
      convert hh using 1 <;> simp only [bipAdj] <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
