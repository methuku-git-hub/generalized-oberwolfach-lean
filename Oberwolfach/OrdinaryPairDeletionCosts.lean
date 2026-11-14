module

public import Oberwolfach.OrdinaryWheelCodegrees

@[expose] public section

/-! Root-omitted pair loads. Edges disjoint from the fixed root vertices
have the extra inverse-order factor needed for a degree-based deletion bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}

def ordinaryOmittedPairLoad (w : OrdinaryWheel Q F H r → ℝ) (e f : Sym2 V⊕(V×U)) : ℝ :=
  ∑ W,if e∈ordinaryWheelResources W ∧ f∈ordinaryWheelResources W ∧ f≠e then w W else 0

theorem ordinaryOmittedPairLoad_nonneg (w : OrdinaryWheel Q F H r → ℝ)
    (hw : ∀ W,0≤w W) (e f : Sym2 V⊕(V×U)) : 0≤ordinaryOmittedPairLoad w e f := by
  exact Finset.sum_nonneg (fun W _=>by split_ifs;exact hw W;exact le_refl _)

theorem ordinaryOmittedPairLoad_self (w : OrdinaryWheel Q F H r → ℝ) (e : Sym2 V⊕(V×U)) :
    ordinaryOmittedPairLoad w e e=0 := by
  simp only [ordinaryOmittedPairLoad,ne_eq,not_true_eq_false,and_false,ite_false,Finset.sum_const_zero]

theorem ordinaryOmittedPairLoad_symm (w : OrdinaryWheel Q F H r → ℝ) (e f : Sym2 V⊕(V×U)) :
    ordinaryOmittedPairLoad w e f=ordinaryOmittedPairLoad w f e := by
  unfold ordinaryOmittedPairLoad
  apply Finset.sum_congr rfl
  intro W _
  by_cases h : e=f
  · subst f;simp
  · simp only [ne_eq,h,Ne.symm h,not_false_eq_true,and_true,true_and,and_comm,and_left_comm,and_assoc]

theorem ordinaryOmittedPairLoad_of_ne (w : OrdinaryWheel Q F H r → ℝ)
    (e f : Sym2 V⊕(V×U)) (h : e≠f) :
    ordinaryOmittedPairLoad w e f=∑ W,if e∈ordinaryWheelResources W ∧ f∈ordinaryWheelResources W then w W else 0 := by
  unfold ordinaryOmittedPairLoad
  apply Finset.sum_congr rfl
  intro W _
  simp only [ne_eq,Ne.symm h,not_false_eq_true,and_true]

variable (Q F H r) (hr : 2≤r) (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (w : OrdinaryWheel Q F H r → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^(r-1))
include hr hn hu hB hw

theorem ordinaryOmittedPairLoad_uniform (e f : Sym2 V⊕(V×U)) :
    ordinaryOmittedPairLoad w e f≤(r:ℝ)^4*B/Fintype.card V := by
  by_cases hef : e=f
  · subst f;rw [ordinaryOmittedPairLoad_self];positivity
  rw [ordinaryOmittedPairLoad_of_ne w e f hef]
  exact ordinary_wheel_physical_pair_load Q F H r hr hn hu w B hB hw e f hef

theorem ordinaryOmittedPairLoad_rim_cost (x y z t : V) (hxy : x≠y) :
    ordinaryOmittedPairLoad w (Sum.inl s(x,y)) (Sum.inl s(z,t))≤
      if z∈({x,y}:Finset V) ∨ t∈({x,y}:Finset V)
      then (r:ℝ)^4*B/Fintype.card V else (r:ℝ)^4*B/(Fintype.card V:ℝ)^2 := by
  by_cases hi : z∈({x,y}:Finset V) ∨ t∈({x,y}:Finset V)
  · rw [if_pos hi]
    exact ordinaryOmittedPairLoad_uniform Q F H r hr hn hu w B hB hw _ _
  rw [if_neg hi]
  by_cases hzt : z=t
  · subst t
    simp only [ordinaryOmittedPairLoad,ordinaryWheelResources_rim,SimpleGraph.mem_edgeSet,
      SimpleGraph.irrefl,false_and,and_false,ite_false,Finset.sum_const_zero]
    positivity
  have hz : z≠x ∧ z≠y := by simpa only [not_or,Finset.mem_insert,Finset.mem_singleton] using (not_or.mp hi).1
  have ht : t≠x ∧ t≠y := by simpa only [not_or,Finset.mem_insert,Finset.mem_singleton] using (not_or.mp hi).2
  have he : (Sum.inl s(x,y):Sym2 V⊕(V×U))≠Sum.inl s(z,t) := by
    intro he
    have he' := Sum.inl.inj he
    have hm : z∈s(x,y) := by rw [he'];simp
    simp only [Sym2.mem_iff] at hm
    tauto
  rw [ordinaryOmittedPairLoad_of_ne w _ _ he]
  simp only [ordinaryWheelResources_rim,SimpleGraph.mem_edgeSet]
  have hh := ordinary_wheel_disjoint_rim_pair Q F H r hr hn w B hB hw hu x y z t hxy
    hz.1.symm ht.1.symm hz.2.symm ht.2.symm hzt
  convert hh using 1
  all_goals
    apply Finset.sum_congr
    · ext W;simp
    · intro W _;split_ifs <;> rfl

theorem ordinaryOmittedPairLoad_rim_spoke_cost (x y z : V) (u : U) (hxy : x≠y) :
    ordinaryOmittedPairLoad w (Sum.inl s(x,y)) (Sum.inr (z,u))≤
      if z∈({x,y}:Finset V) then (r:ℝ)^4*B/Fintype.card V
      else (r:ℝ)^4*B/(Fintype.card V:ℝ)^2 := by
  by_cases hz : z∈({x,y}:Finset V)
  · rw [if_pos hz]
    exact ordinaryOmittedPairLoad_uniform Q F H r hr hn hu w B hB hw _ _
  rw [if_neg hz,ordinaryOmittedPairLoad_of_ne w _ _ (by simp)]
  simp only [ordinaryWheelResources_rim,ordinaryWheelResources_spoke,SimpleGraph.mem_edgeSet]
  have hz' : z≠x ∧ z≠y := by simpa only [not_or,Finset.mem_insert,Finset.mem_singleton] using hz
  have hh := ordinary_wheel_rim_spoke_offroot Q F H r hr hn w B hB hw x y z hxy hz'.1.symm hz'.2.symm u
  have hb : (r:ℝ)^3*B/(Fintype.card V:ℝ)^2≤(r:ℝ)^4*B/(Fintype.card V:ℝ)^2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ hB
    exact pow_le_pow_right₀ (by exact_mod_cast (show 1≤r by omega)) (by omega)
  have ht := hh.trans hb
  convert ht using 1
  all_goals
    apply Finset.sum_congr
    · ext W;simp
    · intro W _;split_ifs <;> rfl

theorem ordinaryOmittedPairLoad_spoke_rim_cost (v x y : V) (u : U) :
    ordinaryOmittedPairLoad w (Sum.inr (v,u)) (Sum.inl s(x,y))≤
      if x=v ∨ y=v then (r:ℝ)^4*B/Fintype.card V
      else (r:ℝ)^4*B/(Fintype.card V:ℝ)^2 := by
  by_cases hv : x=v ∨ y=v
  · rw [if_pos hv]
    exact ordinaryOmittedPairLoad_uniform Q F H r hr hn hu w B hB hw _ _
  rw [if_neg hv,ordinaryOmittedPairLoad_symm]
  by_cases hxy : x=y
  · subst y
    simp only [ordinaryOmittedPairLoad,ordinaryWheelResources_rim,SimpleGraph.mem_edgeSet,
      SimpleGraph.irrefl,false_and,ite_false,Finset.sum_const_zero]
    positivity
  have hh := ordinaryOmittedPairLoad_rim_spoke_cost Q F H r hr hn hu w B hB hw x y v u hxy
  have hnmem : v∉({x,y}:Finset V) := by
    simp only [Finset.mem_insert,Finset.mem_singleton]
    rcases not_or.mp hv with ⟨hx,hy⟩
    exact fun h=>h.elim (fun h=>hx h.symm) (fun h=>hy h.symm)
  simpa only [if_neg hnmem] using hh

theorem ordinaryOmittedPairLoad_spokes_cost (v x : V) (u t : U) :
    ordinaryOmittedPairLoad w (Sum.inr (v,u)) (Sum.inr (x,t))≤
      if t=u then (r:ℝ)^4*B/Fintype.card V else 0 := by
  by_cases htu : t=u
  · rw [if_pos htu]
    exact ordinaryOmittedPairLoad_uniform Q F H r hr hn hu w B hB hw _ _
  rw [if_neg htu]
  unfold ordinaryOmittedPairLoad
  have hz (W : OrdinaryWheel Q F H r) :
      ¬(Sum.inr (v,u)∈ordinaryWheelResources W ∧ Sum.inr (x,t)∈ordinaryWheelResources W ∧
        (Sum.inr (x,t):Sym2 V⊕(V×U))≠Sum.inr (v,u)) := by
    simp only [ordinaryWheelResources_spoke]
    intro h
    exact htu (h.2.1.1.symm.trans h.1.1)
  simp only [hz,ite_false,Finset.sum_const_zero,le_refl]

end Oberwolfach
