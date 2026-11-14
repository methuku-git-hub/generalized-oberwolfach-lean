module

public import Oberwolfach.OrdinaryRimPairCodegrees
public import Oberwolfach.OrdinaryPotentialLoads

@[expose] public section

/-! The physical wheel hypergraph has weighted codegree O(1/n). This
compares distinct physical edges and counts each actual wheel once. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 300000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (Q F : SimpleGraph V) (H : V → U → Prop) (r : ℕ) (hr : 2≤r) (hn : 0<Fintype.card V)
    (hu : Fintype.card U≤Fintype.card V)
    (w : OrdinaryWheel Q F H r → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^(r-1))
include hr hn hu hB hw

theorem ordinary_wheel_physical_pair_load (e f : Sym2 V⊕(V×U)) (hef : e≠f) :
    (∑ W,if e∈ordinaryWheelResources W ∧ f∈ordinaryWheelResources W then w W else 0)≤
      (r:ℝ)^4*B/Fintype.card V := by
  have hn1 : (1:ℝ)≤Fintype.card V := by exact_mod_cast (show 1≤Fintype.card V by omega)
  have hr1 : (1:ℝ)≤r := by exact_mod_cast (show 1≤r by omega)
  have hs : (r:ℝ)^2*B/Fintype.card V≤(r:ℝ)^4*B/Fintype.card V := by
    simpa only [pow_one] using uniform_wheel_pair_scale _ _ B hn1 hr1 hB 2 1 (by omega) (by omega)
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      induction e using Sym2.ind with
      | _ x y =>
        induction f using Sym2.ind with
        | _ z t =>
          simp only [ordinaryWheelResources_rim,SimpleGraph.mem_edgeSet] at *
          by_cases hxy : x=y
          · subst y;simp only [SimpleGraph.irrefl,and_false,false_and,ite_false,Finset.sum_const_zero];positivity
          by_cases hzt : z=t
          · subst t;simp only [SimpleGraph.irrefl,and_false,false_and,ite_false,Finset.sum_const_zero];positivity
          have hh := ordinary_wheel_distinct_rim_pair Q F H r hr hn hu w B hB hw x y z t hxy hzt
            (fun h=>hef (congrArg Sum.inl h))
          convert hh using 1
    | inr f =>
      rcases f with ⟨z,u⟩
      induction e using Sym2.ind with
      | _ x y =>
        simp only [ordinaryWheelResources_rim,ordinaryWheelResources_spoke,SimpleGraph.mem_edgeSet]
        by_cases hxy : x=y
        · subst y;simp only [SimpleGraph.irrefl,false_and,ite_false,Finset.sum_const_zero];positivity
        have hh := (ordinary_wheel_rim_spoke_pair Q F H r hr hn w B hB hw x y hxy z u).trans hs
        convert hh using 1
  | inr e =>
    rcases e with ⟨x,u⟩
    cases f with
    | inl f =>
      induction f using Sym2.ind with
      | _ z t =>
        simp only [ordinaryWheelResources_rim,ordinaryWheelResources_spoke,SimpleGraph.mem_edgeSet]
        by_cases hzt : z=t
        · subst t;simp only [SimpleGraph.irrefl,and_false,ite_false,Finset.sum_const_zero];positivity
        have hh := (ordinary_wheel_rim_spoke_pair Q F H r hr hn w B hB hw z t hzt x u).trans hs
        simpa only [and_comm] using hh
    | inr f =>
      rcases f with ⟨y,v⟩
      simp only [ordinaryWheelResources_spoke]
      by_cases huv : u=v
      · subst v
        have hxy : x≠y := by intro he;subst y;exact hef rfl
        have hh := (ordinary_wheel_spoke_pair Q F H r hr hn w B hB hw x y hxy u).trans hs
        simpa only [and_assoc,and_left_comm,and_self_left] using hh
      · have hz (W : OrdinaryWheel Q F H r) :
            ¬((ordinaryWheelHub W=u ∧ x∈(ordinaryWheelRim W).support) ∧
              (ordinaryWheelHub W=v ∧ y∈(ordinaryWheelRim W).support)) :=
            fun h=>huv (h.1.1.symm.trans h.2.1)
        simp only [hz,ite_false,Finset.sum_const_zero]
        positivity

end Oberwolfach
