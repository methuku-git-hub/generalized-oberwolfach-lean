module

public import Oberwolfach.OrdinaryCyclePairLoads
public import Oberwolfach.RelationIncidentWeights

@[expose] public section

/-! Explicit weighted losses from requiring the vertices of a cycle to
be independent in a fixed bounded-degree conflict graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_weighted_union_bound {I J : Type*} [Fintype I] [Fintype J]
    (w : I → ℝ) (hw : ∀ i,0≤w i) (base : I → Prop) (E : I → J → Prop) :
    (∑ i,if base i ∧ ∃ j,E i j then w i else 0)≤
      ∑ j,∑ i,if base i ∧ E i j then w i else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  by_cases h : base i ∧ ∃ j,E i j
  · obtain ⟨hb,j,hj⟩:=h
    rw [if_pos ⟨hb,j,hj⟩]
    have hh:=Finset.single_le_sum (s:=Finset.univ)
      (f:=fun j=>if base i ∧ E i j then w i else 0)
      (fun j _=>by split_ifs;exact hw i;exact le_refl _) (Finset.mem_univ j)
    simpa only [hb,hj,and_self,ite_true] using hh
  · rw [if_neg h]
    exact Finset.sum_nonneg (fun j _=>by split_ifs;exact hw i;exact le_refl _)

variable {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V) (r : ℕ) (hr : 2≤r) (hn : 0<Fintype.card V)
    (weight : OrdinaryCycle P r → ℝ) (hweight : ∀ C,0≤weight C)
    (B : ℝ) (hB : 0≤B) (hb : ∀ C,weight C≤B/(Fintype.card V:ℝ)^(r-2))
include hr hn hweight hB hb

theorem ordinary_cycle_three_vertex_weight (x y z : V) (hxy : x≠y) (hxz : x≠z) (hyz : y≠z)
    (E : OrdinaryCycle P r → Prop)
    (hE : ∀ C,E C → x∈C.val.val.support ∧ y∈C.val.val.support ∧ z∈C.val.val.support) :
    (∑ C,if E C then weight C else 0)≤(r:ℝ)^4*B/Fintype.card V := by
  have hc : ({x,y,z}:Finset V).card=3 := by simp [hxy,hxz,hyz]
  have hh := ordinary_cycle_event_weight_bound P r (by omega) hn weight hweight B hB hb {x,y,z}
    (by rw [hc];norm_num) E (by
      intro C h v hv
      rcases hE C h with ⟨hx,hy,hz⟩
      simp only [Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] at hv
      rcases hv with rfl|rfl|rfl <;> assumption)
  simp only [hc,show 3-2=1 from rfl,pow_one] at hh
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ hB
  exact pow_le_pow_right₀ (by exact_mod_cast (show 1≤r by omega)) (by omega)

theorem ordinary_cycle_four_vertex_weight (x y z t : V)
    (hxy : x≠y) (hxz : x≠z) (hxt : x≠t) (hyz : y≠z) (hyt : y≠t) (hzt : z≠t)
    (E : OrdinaryCycle P r → Prop)
    (hE : ∀ C,E C → x∈C.val.val.support ∧ y∈C.val.val.support ∧ z∈C.val.val.support ∧ t∈C.val.val.support) :
    (∑ C,if E C then weight C else 0)≤(r:ℝ)^4*B/(Fintype.card V:ℝ)^2 := by
  have hc : ({x,y,z,t}:Finset V).card=4 := by simp [hxy,hxz,hxt,hyz,hyt,hzt]
  have hh := ordinary_cycle_event_weight_bound P r (by omega) hn weight hweight B hB hb {x,y,z,t}
    (by rw [hc];norm_num) E (by
      intro C h v hv
      rcases hE C h with ⟨hx,hy,hz,ht⟩
      simp only [Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] at hv
      rcases hv with rfl|rfl|rfl|rfl <;> assumption)
  simpa only [hc,show 4-2=2 from rfl] using hh

theorem ordinary_cycle_rim_conflict_pair (F : SimpleGraph V) (x y z t : V)
    (hxy : x≠y) (hFxy : ¬F.Adj x y) (hzt : F.Adj z t) :
    (∑ C,if C.val.val.Adj x y ∧ z∈C.val.val.support ∧ t∈C.val.val.support then weight C else 0)≤
      if z∈({x,y}:Finset V) ∨ t∈({x,y}:Finset V) then (r:ℝ)^4*B/Fintype.card V
      else (r:ℝ)^4*B/(Fintype.card V:ℝ)^2 := by
  let E := fun C : OrdinaryCycle P r=>C.val.val.Adj x y ∧ z∈C.val.val.support ∧ t∈C.val.val.support
  have hs (C : OrdinaryCycle P r) (h : E C) : x∈C.val.val.support ∧ y∈C.val.val.support :=
    ⟨h.1.mem_support_left,h.1.mem_support_right⟩
  by_cases hnear : z∈({x,y}:Finset V) ∨ t∈({x,y}:Finset V)
  · rw [if_pos hnear]
    by_cases hz : z∈({x,y}:Finset V)
    · have ht : t≠x ∧ t≠y := by
        simp only [Finset.mem_insert,Finset.mem_singleton] at hz
        rcases hz with rfl|rfl
        · exact ⟨hzt.ne.symm,fun h=>hFxy (h ▸ hzt)⟩
        · exact ⟨fun h=>hFxy (h ▸ hzt.symm),hzt.ne.symm⟩
      convert ordinary_cycle_three_vertex_weight P r hr hn weight hweight B hB hb x y t hxy ht.1.symm ht.2.symm E
        (fun C h=>⟨(hs C h).1,(hs C h).2,h.2.2⟩) using 1 <;> congr!
    · have hz' : z≠x ∧ z≠y := by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hz
      convert ordinary_cycle_three_vertex_weight P r hr hn weight hweight B hB hb x y z hxy hz'.1.symm hz'.2.symm E
        (fun C h=>⟨(hs C h).1,(hs C h).2,h.2.1⟩) using 1 <;> congr!
  · rw [if_neg hnear]
    have hz : z≠x ∧ z≠y := by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using (not_or.mp hnear).1
    have ht : t≠x ∧ t≠y := by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using (not_or.mp hnear).2
    convert ordinary_cycle_four_vertex_weight P r hr hn weight hweight B hB hb x y z t hxy hz.1.symm ht.1.symm
      hz.2.symm ht.2.symm hzt.ne E (fun C h=>⟨(hs C h).1,(hs C h).2,h.2.1,h.2.2⟩) using 1 <;> congr!

theorem ordinary_cycle_vertex_conflict_pair (v z t : V) (hzt : z≠t) :
    (∑ C,if v∈C.val.val.support ∧ z∈C.val.val.support ∧ t∈C.val.val.support then weight C else 0)≤
      if z=v ∨ t=v then (r:ℝ)^4*B else (r:ℝ)^4*B/Fintype.card V := by
  by_cases hnear : z=v ∨ t=v
  · rw [if_pos hnear]
    have hc : ({z,t}:Finset V).card=2 := by simp [hzt]
    have hh := ordinary_cycle_event_weight_bound P r (by omega) hn weight hweight B hB hb {z,t}
      (by rw [hc]) (fun C=>v∈C.val.val.support ∧ z∈C.val.val.support ∧ t∈C.val.val.support) (by
        intro C h x hx
        simp only [Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] at hx
        rcases hx with rfl|rfl
        · exact h.2.1
        · exact h.2.2)
    simp only [hc,show 2-2=0 from rfl,pow_zero,div_one] at hh
    have hpow : (r:ℝ)^2*B≤(r:ℝ)^4*B := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact pow_le_pow_right₀ (by exact_mod_cast (show 1≤r by omega)) (by omega)
    convert hh.trans hpow using 1 <;> congr!
  · rw [if_neg hnear]
    convert ordinary_cycle_three_vertex_weight P r hr hn weight hweight B hB hb v z t
      (Ne.symm (not_or.mp hnear).1) (Ne.symm (not_or.mp hnear).2) hzt _ (fun _ h=>h) using 1 <;> congr!


omit hr hn hB hb in
theorem ordinary_cycle_conflict_union (F : SimpleGraph V) (base : OrdinaryCycle P r → Prop) :
    (∑ C,if base C ∧ (∃ z∈C.val.val.support,∃ t∈C.val.val.support,F.Adj z t) then weight C else 0)≤
      ∑ z,∑ t,if F.Adj z t then
        (∑ C,if base C ∧ z∈C.val.val.support ∧ t∈C.val.val.support then weight C else 0) else 0 := by
  have hh := finite_weighted_union_bound weight hweight base
    (fun C (a : V×V)=>F.Adj a.1 a.2 ∧ a.1∈C.val.val.support ∧ a.2∈C.val.val.support)
  have he (C : OrdinaryCycle P r) :
      (∃ a : V×V,F.Adj a.1 a.2 ∧ a.1∈C.val.val.support ∧ a.2∈C.val.val.support)↔
      ∃ z∈C.val.val.support,∃ t∈C.val.val.support,F.Adj z t := by
    constructor
    · rintro ⟨⟨z,t⟩,hF,hz,ht⟩;exact ⟨z,hz,t,ht,hF⟩
    · rintro ⟨z,hz,t,ht,hF⟩;exact ⟨(z,t),hF,hz,ht⟩
  simp only [he] at hh
  rw [Fintype.sum_prod_type] at hh
  apply hh.trans_eq
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro t _
  by_cases hf : F.Adj z t
  · simp only [hf,true_and,ite_true]
  · simp only [hf,false_and,and_false,ite_false,Finset.sum_const_zero]

theorem ordinary_cycle_rim_conflict_loss (F : SimpleGraph V) (L : ℝ)
    (hdeg : ∀ v,(F.degree v:ℝ)≤L) (x y : V) (hxy : x≠y) (hFxy : ¬F.Adj x y) :
    (∑ C,if C.val.val.Adj x y ∧ (∃ z∈C.val.val.support,∃ t∈C.val.val.support,F.Adj z t)
      then weight C else 0)≤5*(r:ℝ)^4*B*L/Fintype.card V := by
  have hrow (v : V) : (∑ u,bipAdj F.Adj v u)≤L := by
    simpa only [bipAdj,graph_adjacency_row_sum] using hdeg v
  have hcol (v : V) : (∑ u,bipAdj F.Adj u v)≤L := by
    simpa only [bipAdj,F.adj_comm] using hrow v
  have hc : ({x,y}:Finset V).card=2 := by simp [hxy]
  have hn0 : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have hcost := relation_root_incident_cost F.Adj L hrow hcol {x,y} {x,y}
    ((r:ℝ)^4*B/Fintype.card V) ((r:ℝ)^4*B/(Fintype.card V:ℝ)^2) (by positivity) (by positivity)
  calc
    _ ≤ ∑ z,∑ t,if F.Adj z t then
        (∑ C,if C.val.val.Adj x y ∧ z∈C.val.val.support ∧ t∈C.val.val.support then weight C else 0) else 0 :=
      ordinary_cycle_conflict_union P r weight hweight F (fun C=>C.val.val.Adj x y)
    _ ≤ ∑ z,∑ t,if F.Adj z t then
        (if z∈({x,y}:Finset V) ∨ t∈({x,y}:Finset V) then (r:ℝ)^4*B/Fintype.card V
          else (r:ℝ)^4*B/(Fintype.card V:ℝ)^2) else 0 := by
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro t _
      by_cases hzt : F.Adj z t
      · simp only [hzt,ite_true]
        exact ordinary_cycle_rim_conflict_pair P r hr hn weight hweight B hB hb F x y z t hxy hFxy hzt
      · simp only [hzt,ite_false,le_refl]
    _ ≤ L*((2+2)*((r:ℝ)^4*B/Fintype.card V)+(Fintype.card V:ℝ)*((r:ℝ)^4*B/(Fintype.card V:ℝ)^2)) := by
      simpa only [hc,Nat.cast_ofNat] using hcost
    _ = _ := by field_simp [ne_of_gt hn0];ring

set_option backward.isDefEq.respectTransparency true in
theorem ordinary_cycle_vertex_conflict_loss (F : SimpleGraph V) (L : ℝ)
    (hdeg : ∀ v,(F.degree v:ℝ)≤L) (v : V) :
    (∑ C,if v∈C.val.val.support ∧ (∃ z∈C.val.val.support,∃ t∈C.val.val.support,F.Adj z t)
      then weight C else 0)≤3*(r:ℝ)^4*B*L := by
  have hrow (v : V) : (∑ u,bipAdj F.Adj v u)≤L := by
    simpa only [bipAdj,graph_adjacency_row_sum] using hdeg v
  have hcol (v : V) : (∑ u,bipAdj F.Adj u v)≤L := by
    simpa only [bipAdj,F.adj_comm] using hrow v
  have hn0 : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have hcost := relation_root_incident_cost F.Adj L hrow hcol {v} {v}
    ((r:ℝ)^4*B) ((r:ℝ)^4*B/Fintype.card V) (by positivity) (by positivity)
  calc
    _ ≤ ∑ z,∑ t,if F.Adj z t then
        (∑ C,if v∈C.val.val.support ∧ z∈C.val.val.support ∧ t∈C.val.val.support then weight C else 0) else 0 :=
      by convert ordinary_cycle_conflict_union P r weight hweight F (fun C=>v∈C.val.val.support) using 1 <;> congr!
    _ ≤ ∑ z,∑ t,if F.Adj z t then
        (if z=v ∨ t=v then (r:ℝ)^4*B else (r:ℝ)^4*B/Fintype.card V) else 0 := by
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro t _
      by_cases hzt : F.Adj z t
      · simp only [hzt,ite_true]
        convert ordinary_cycle_vertex_conflict_pair P r hr hn weight hweight B hB hb v z t hzt.ne using 1 <;> congr!
      · simp only [hzt,ite_false,le_refl]
    _ ≤ L*((1+1)*((r:ℝ)^4*B)+(Fintype.card V:ℝ)*((r:ℝ)^4*B/Fintype.card V)) := by
      simpa only [Finset.card_singleton,Finset.mem_singleton,Nat.cast_one] using hcost
    _ = _ := by field_simp [ne_of_gt hn0];ring

end Oberwolfach
