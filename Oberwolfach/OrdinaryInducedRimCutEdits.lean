module

public import Oberwolfach.OrdinaryInducedOrientationCommutation
public import Oberwolfach.OrdinaryEditedCutsFromSample

@[expose] public section
/-! The fixed inner orientation cut survives bounded symmetric rim edits,
    using exactly the original physical direction coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]

theorem ordinary_induced_changed_rim_bound (Qraw Q:SimpleGraph V) (I:Finset V) (v:I):
    ((changed ((Qraw.induce (I:Set V)).neighborFinset v) ((Q.induce (I:Set V)).neighborFinset v)).card:ℝ)≤
      ((changed (Qraw.neighborFinset v.val) (Q.neighborFinset v.val)).card:ℝ):=by
  have h:(changed ((Qraw.induce (I:Set V)).neighborFinset v) ((Q.induce (I:Set V)).neighborFinset v)).card≤
      (changed (Qraw.neighborFinset v.val) (Q.neighborFinset v.val)).card:=by
    apply Finset.card_le_card_of_injOn Subtype.val
    · intro w hw
      change w ∈ changed ((Qraw.induce (I:Set V)).neighborFinset v) ((Q.induce (I:Set V)).neighborFinset v) at hw
      change w.val ∈ changed (Qraw.neighborFinset v.val) (Q.neighborFinset v.val)
      simp only [changed,Finset.mem_union,Finset.mem_sdiff,SimpleGraph.mem_neighborFinset,
        SimpleGraph.induce_adj] at hw ⊢
      exact hw
    · intro a _ b _ hab;exact Subtype.val_injective hab
  exact_mod_cast h

theorem ordinary_induced_rim_cut_after_edits
    (Qraw Q:SimpleGraph V) (I:Finset V) (coins:Sym2 V→Bool) (δ h ζ L:ℝ)
    (hI:0<I.card) (hζ:0≤ζ) (hscale:L≤ζ*I.card)
    (hedit:∀v,((changed (Qraw.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L)
    (hcut:BipartiteLargeCut (fun x y:I=>sampledOrientation Qraw coins x.val y.val) δ h):
    let localCoins:=fun e:Sym2 I=>coins (Sym2.map (⟨Subtype.val,Subtype.val_injective⟩:I↪V) e);
    let R:=ordinarySampledOrientedRelation (Q.induce (I:Set V)) localCoins;
    (∀x y,relationMultiplicity R x y+relationMultiplicity R y x=if (Q.induce (I:Set V)).Adj x y then 1 else 0) ∧
    BipartiteLargeCut (relationMultiplicity R) δ (h-ζ):=by
  intro localCoins R
  let A:=ordinarySampledOrientedRelation (Qraw.induce (I:Set V)) localCoins
  have hn:0<Fintype.card I:=by simpa only [Fintype.card_coe] using hI
  have hbase:BipartiteLargeCut (relationMultiplicity A) δ h:=by
    rw [←ordinary_sampled_orientation_as_relation]
    have he:=ordinary_induced_sampled_orientation Qraw I coins
    change sampledOrientation (Qraw.induce (I:Set V)) localCoins=_ at he
    rw [he]
    exact hcut
  have hchange:∀v:I,((changed ((Qraw.induce (I:Set V)).neighborFinset v)
      ((Q.induce (I:Set V)).neighborFinset v)).card:ℝ)≤L:=by
    intro v
    exact (ordinary_induced_changed_rim_bound Qraw Q I v).trans (hedit v.val)
  have hp (x y:I):¬(A x y↔R x y)→¬((Qraw.induce (I:Set V)).Adj x y↔(Q.induce (I:Set V)).Adj x y):=by
    intro horient heq
    apply horient
    dsimp [A,R,ordinarySampledOrientedRelation]
    rw [heq]
  have hrow:∀x:I,(∑y,if ¬(A x y↔R x y) then (1:ℝ) else 0)≤ζ*Fintype.card I:=by
    intro x
    have hh:(∑y,if ¬((Qraw.induce (I:Set V)).Adj x y↔(Q.induce (I:Set V)).Adj x y) then (1:ℝ) else 0)≤L:=by
      have h:=hchange x
      simp only [SimpleGraph.neighborFinset_eq_filter] at h
      convert (ordinary_relation_change_sum ((Qraw.induce (I:Set V)).Adj x) ((Q.induce (I:Set V)).Adj x)).le.trans h using 1 <;>
        congr! 8 <;> exact Subsingleton.elim _ _
    have hi:(∑y,if ¬(A x y↔R x y) then (1:ℝ) else 0)≤
        ∑y,if ¬((Qraw.induce (I:Set V)).Adj x y↔(Q.induce (I:Set V)).Adj x y) then (1:ℝ) else 0:=by
      apply Finset.sum_le_sum
      intro y _
      by_cases he:¬(A x y↔R x y)
      · have hp':¬(Qraw.Adj x.val y.val↔Q.Adj x.val y.val):=hp x y he
        simp [he,hp']
      · simp only [if_neg he];split_ifs <;> norm_num
    exact hi.trans (hh.trans (by simpa only [Fintype.card_coe] using hscale))
  have hcol:∀y:I,(∑x,if ¬(A x y↔R x y) then (1:ℝ) else 0)≤ζ*Fintype.card I:=by
    intro y
    have hh:(∑x,if ¬((Qraw.induce (I:Set V)).Adj x y↔(Q.induce (I:Set V)).Adj x y) then (1:ℝ) else 0)≤L:=by
      have hs:(∑x,if ¬((Qraw.induce (I:Set V)).Adj x y↔(Q.induce (I:Set V)).Adj x y) then (1:ℝ) else 0)=
          ∑x,if ¬((Qraw.induce (I:Set V)).Adj y x↔(Q.induce (I:Set V)).Adj y x) then (1:ℝ) else 0:=by
        apply Finset.sum_congr rfl
        intro x _
        by_cases h1:Qraw.Adj x.val y.val <;> by_cases h2:Q.Adj x.val y.val <;>
          simp [SimpleGraph.induce_adj,Qraw.adj_comm,Q.adj_comm,h1,h2]
      rw [hs]
      have h:=hchange y
      simp only [SimpleGraph.neighborFinset_eq_filter] at h
      convert (ordinary_relation_change_sum ((Qraw.induce (I:Set V)).Adj y) ((Q.induce (I:Set V)).Adj y)).le.trans h using 1 <;>
        congr! 8 <;> exact Subsingleton.elim _ _
    have hi:(∑x,if ¬(A x y↔R x y) then (1:ℝ) else 0)≤
        ∑x,if ¬((Qraw.induce (I:Set V)).Adj x y↔(Q.induce (I:Set V)).Adj x y) then (1:ℝ) else 0:=by
      apply Finset.sum_le_sum
      intro x _
      by_cases he:¬(A x y↔R x y)
      · have hp':¬(Qraw.Adj x.val y.val↔Q.Adj x.val y.val):=hp x y he
        simp [he,hp']
      · simp only [if_neg he];split_ifs <;> norm_num
    exact hi.trans (hh.trans (by simpa only [Fintype.card_coe] using hscale))
  have hnew:=bipartiteLargeCut_after_relation_changes hn hn A R δ h ζ hζ hrow hcol hbase
  refine ⟨?_,hnew⟩
  intro x y
  rw [←ordinary_sampled_orientation_as_relation]
  exact sampledOrientation_physical (Q.induce (I:Set V)) localCoins x y
end Oberwolfach
