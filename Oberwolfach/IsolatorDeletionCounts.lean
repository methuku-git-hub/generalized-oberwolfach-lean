module

public import Oberwolfach.IsolatorConfigurationCounts
public import Oberwolfach.OrdinaryRimPairCodegrees
public import Oberwolfach.RelationIncidentWeights

@[expose] public section

/-! Counts of isolator configurations containing prescribed deleted edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
  {P Q F : SimpleGraph V} {H : V → U → Prop} {k : ℕ} {θ α : ℝ} {x y : V}

theorem isolator_configuration_root_count (R : Finset V) (hR : R.card≤k) :
    (∑ T : OrdinaryIsolatorConfiguration P Q F H k θ α x y,
      if R⊆T.vertices.val then (1 : ℝ) else 0)≤
        Fintype.card U*(Fintype.card V : ℝ)^(k-R.card) := by
  calc
    _ = ∑ u : U,∑ T : OrdinaryIsolatorConfiguration P Q F H k θ α x y,
        if T.hub=u ∧ R⊆T.vertices.val then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro T _
      by_cases hh : R⊆T.vertices.val
      · simp only [hh,and_true,ite_true]
        simp
      · simp only [hh,and_false,ite_false,Finset.sum_const_zero]
    _ ≤ ∑ _ : U,(Fintype.card V : ℝ)^(k-R.card) :=
      Finset.sum_le_sum (fun u _=>isolator_configuration_hub_root_count u R hR)
    _ = _ := by simp

theorem isolator_vertex_pair_count (hxy : x≠y) (hk : 4≤k)
    (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (z t : V) (hzt : z≠t) (he : s(x,y)≠s(z,t)) :
    (∑ T : OrdinaryIsolatorConfiguration P Q F H k θ α x y,
      if z∈T.vertices.val ∧ t∈T.vertices.val then (1 : ℝ) else 0)≤
        if z∈({x,y} : Finset V) ∨ t∈({x,y} : Finset V)
        then (Fintype.card V : ℝ)^(k-2) else (Fintype.card V : ℝ)^(k-3) := by
  have hc := distinct_pair_union_card x y z t hxy hzt he
  have hRk : ({x,y,z,t} : Finset V).card≤k := hc.2.trans hk
  have hh := isolator_configuration_root_count (P:=P) (Q:=Q) (F:=F) (H:=H)
    (k:=k) (θ:=θ) (α:=α) (x:=x) (y:=y) {x,y,z,t} hRk
  have hs : (∑ T : OrdinaryIsolatorConfiguration P Q F H k θ α x y,
      if z∈T.vertices.val ∧ t∈T.vertices.val then (1 : ℝ) else 0)=
      (∑ T : OrdinaryIsolatorConfiguration P Q F H k θ α x y,
      if ({x,y,z,t} : Finset V)⊆T.vertices.val then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro T _
    simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff,T.endpoints.1,T.endpoints.2,true_and]
  rw [hs]
  have hn1 : (1 : ℝ)≤Fintype.card V := by exact_mod_cast hn
  have huR : (Fintype.card U : ℝ)≤Fintype.card V := by exact_mod_cast hu
  have bound (a : ℕ) (ha : a≤({x,y,z,t} : Finset V).card) (hak : a≤k) :
      (Fintype.card U : ℝ)*(Fintype.card V : ℝ)^(k-({x,y,z,t} : Finset V).card)≤
        (Fintype.card V : ℝ)^(k-a+1) := by
    calc
      _ ≤ (Fintype.card V : ℝ)*(Fintype.card V : ℝ)^(k-a) :=
        mul_le_mul huR (pow_le_pow_right₀ hn1 (Nat.sub_le_sub_left ha k))
          (by positivity) (Nat.cast_nonneg _)
      _ = _ := by rw [pow_succ];ring
  by_cases hi : z∈({x,y} : Finset V) ∨ t∈({x,y} : Finset V)
  · rw [if_pos hi]
    have hb := bound 3 hc.1 (by omega)
    have heq : k-3+1=k-2 := by omega
    rw [heq] at hb
    exact hh.trans hb
  · rw [if_neg hi]
    have hz : z≠x ∧ z≠y := by simpa only [not_or,Finset.mem_insert,Finset.mem_singleton] using (not_or.mp hi).1
    have ht : t≠x ∧ t≠y := by simpa only [not_or,Finset.mem_insert,Finset.mem_singleton] using (not_or.mp hi).2
    have hcard : ({x,y,z,t} : Finset V).card=4 := by simp [hxy,hz.1.symm,hz.2.symm,ht.1.symm,ht.2.symm,hzt]
    have hb := bound 4 (by rw [hcard]) hk
    have heq : k-4+1=k-3 := by omega
    rw [heq] at hb
    exact hh.trans hb

theorem isolator_spoke_count (hxy : x≠y) (hk : 3≤k) (z : V) (u : U) :
    (∑ T : OrdinaryIsolatorConfiguration P Q F H k θ α x y,
      if T.hub=u ∧ z∈T.vertices.val then (1 : ℝ) else 0)≤
        if z∈({x,y} : Finset V) then (Fintype.card V : ℝ)^(k-2)
        else (Fintype.card V : ℝ)^(k-3) := by
  by_cases hz : z∈({x,y} : Finset V)
  · rw [if_pos hz]
    apply le_trans ?_ (isolator_configuration_hub_count (P:=P) (Q:=Q) (F:=F) (H:=H)
      (k:=k) (θ:=θ) (α:=α) (x:=x) (y:=y) u hxy (by omega))
    apply Finset.sum_le_sum
    intro T _
    split_ifs <;> norm_num
    all_goals tauto
  · rw [if_neg hz]
    have hzx : z≠x ∧ z≠y := by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hz
    have hc : ({x,y,z} : Finset V).card=3 := by simp [hxy,hzx.1.symm,hzx.2.symm]
    have hh := isolator_configuration_hub_root_count (P:=P) (Q:=Q) (F:=F) (H:=H)
      (k:=k) (θ:=θ) (α:=α) (x:=x) (y:=y) u {x,y,z} (by rw [hc];exact hk)
    rw [hc] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro T _
    simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff,T.endpoints.1,T.endpoints.2,true_and]

end Oberwolfach
