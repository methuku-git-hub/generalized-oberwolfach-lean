module

public import Oberwolfach.TransferConfigurationCounts
public import Oberwolfach.RelationIncidentWeights

@[expose] public section

/-! Counts of actual transfer configurations affected by a specified
physical edge. The fixed rim root is not a free label. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [DecidableEq V]
  {r : ℕ} {hr : 3≤r} {Q F : SimpleGraph V} {H : V → U → Prop}
  {v : V} {u u' : U}

theorem transfer_free_vertex_count (z : V) :
    (∑ T : OrdinaryTransferConfiguration hr Q F H v u u',
      if z∈Set.range T.labels then (1 : ℝ) else 0)≤
        (r : ℝ)^2*(Fintype.card V : ℝ)^(r^2-1) := by
  have hh := ordinary_transfer_configuration_root_count (hr:=hr) (Q:=Q) (F:=F)
    (H:=H) (v:=v) (u:=u) (u':=u') {z}
  simpa only [Finset.coe_singleton,Set.singleton_subset_iff,Finset.card_singleton,pow_one] using hh

theorem transfer_free_pair_count (x y : V) (hxy : x≠y) :
    (∑ T : OrdinaryTransferConfiguration hr Q F H v u u',
      if x∈Set.range T.labels ∧ y∈Set.range T.labels then (1 : ℝ) else 0)≤
        (r : ℝ)^4*(Fintype.card V : ℝ)^(r^2-2) := by
  have hh := ordinary_transfer_configuration_root_count (hr:=hr) (Q:=Q) (F:=F)
    (H:=H) (v:=v) (u:=u) (u':=u') {x,y}
  have hc : ({x,y} : Finset V).card=2 := by simp [hxy]
  simp only [hc,Finset.coe_insert,Finset.coe_singleton,Set.insert_subset_iff,Set.singleton_subset_iff] at hh
  convert hh using 1
  ring

theorem transfer_vertex_pair_count (x y : V) (hxy : x≠y) :
    (∑ T : OrdinaryTransferConfiguration hr Q F H v u u',
      if x∈insert v (Set.range T.labels) ∧ y∈insert v (Set.range T.labels) then (1 : ℝ) else 0)≤
        if x=v ∨ y=v then (r : ℝ)^4*(Fintype.card V : ℝ)^(r^2-1)
        else (r : ℝ)^4*(Fintype.card V : ℝ)^(r^2-2) := by
  have hr1 : (1 : ℝ)≤r := by exact_mod_cast (show 1≤r by omega)
  have hp : (r : ℝ)^2≤(r : ℝ)^4 := pow_le_pow_right₀ hr1 (by omega)
  by_cases hx : x=v
  · subst x
    have hy : y≠v := Ne.symm hxy
    simp only [true_or,ite_true,Set.mem_insert_iff,true_or,true_and,hy,false_or]
    exact (transfer_free_vertex_count (hr:=hr) (Q:=Q) (F:=F) (H:=H) (v:=v) (u:=u) (u':=u') y).trans
      (mul_le_mul_of_nonneg_right hp (by positivity))
  · by_cases hy : y=v
    · subst y
      simp only [hx,false_or,true_or,ite_true,Set.mem_insert_iff,hx,false_or,and_true]
      exact (transfer_free_vertex_count (hr:=hr) (Q:=Q) (F:=F) (H:=H) (v:=v) (u:=u) (u':=u') x).trans
        (mul_le_mul_of_nonneg_right hp (by positivity))
    · simp only [hx,hy,false_or,ite_false,Set.mem_insert_iff,hx,hy,false_or]
      exact transfer_free_pair_count x y hxy

/-- Summing all deleted rim edges uses degree bounds at the fixed root
and the total edge bound for pairs of free labels. -/
theorem transfer_deleted_rim_count (D : SimpleGraph V) (d : ℝ)
    (hD : ∀ x,(D.degree x : ℝ)≤d) (hn : 0<Fintype.card V) :
    (∑ x,∑ y,if D.Adj x y then
      (∑ T : OrdinaryTransferConfiguration hr Q F H v u u',
        if x∈insert v (Set.range T.labels) ∧ y∈insert v (Set.range T.labels) then (1 : ℝ) else 0)
      else 0)≤3*(r : ℝ)^4*d*(Fintype.card V : ℝ)^(r^2-1) := by
  let n : ℝ := Fintype.card V
  let M : ℝ := (r : ℝ)^4*n^(r^2-1)
  let N : ℝ := (r : ℝ)^4*n^(r^2-2)
  have hd (x : V) : (∑ y,bipAdj D.Adj x y)≤d := by
    have he : (∑ y,bipAdj D.Adj x y)=(D.degree x : ℝ) := by
      rw [SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter,Finset.card_filter]
      push_cast
      apply Finset.sum_congr rfl
      intro y _
      dsimp [bipAdj]
    rw [he]
    exact hD x
  have hdi (y : V) : (∑ x,bipAdj D.Adj x y)≤d := by
    have he : (∑ x,bipAdj D.Adj x y)=(∑ x,bipAdj D.Adj y x) := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [bipAdj,D.adj_comm]
    rw [he]
    exact hd y
  have hh := relation_root_incident_cost D.Adj d hd hdi {v} {v} M N (by dsimp [M];positivity) (by dsimp [N];positivity)
  simp only [Finset.card_singleton,Nat.cast_one,Finset.mem_singleton] at hh
  calc
    _ ≤ ∑ x,∑ y,if D.Adj x y then (if x=v ∨ y=v then M else N) else 0 := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      by_cases hxy : D.Adj x y
      · simp only [hxy,ite_true]
        exact transfer_vertex_pair_count x y hxy.ne
      · simp only [hxy,ite_false,le_refl]
    _ ≤ d*((1+1)*M+n*N) := hh
    _ = _ := by
      have he : r^2-1=(r^2-2)+1 := by
        have hh2 : 2≤r^2 := by nlinarith
        omega
      dsimp [M,N,n]
      rw [he,pow_succ]
      ring

end Oberwolfach
