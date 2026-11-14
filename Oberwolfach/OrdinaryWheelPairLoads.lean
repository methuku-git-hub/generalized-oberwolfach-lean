module

public import Oberwolfach.OrdinaryWheelEventBounds

@[expose] public section

/-! Pair loads for actual physical ordinary wheels. A fixed spoke fixes
its hub; a rim edge does not. These are counts of wheels, not embeddings. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1900000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (Q F : SimpleGraph V) (H : V → U → Prop) (r : ℕ) (hr : 2≤r) (hn : 0<Fintype.card V)
    (w : OrdinaryWheel Q F H r → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^(r-1))

include hr hn hB hw

theorem ordinary_wheel_fixed_hub_event (S : Finset V) (hS : 2≤S.card) (u : U)
    (P : OrdinaryWheel Q F H r → Prop)
    (hP : ∀ W,P W → (↑S:Set V)⊆(ordinaryWheelRim W).support ∧ ordinaryWheelHub W=u) :
    (∑ W,if P W then w W else 0)≤(r:ℝ)^S.card*B/(Fintype.card V:ℝ)^(S.card-1) := by
  have hh := ordinary_wheel_event_weight_bound Q F H r hr hn w B hB hw S hS {u} P
    (by intro W hp;exact ⟨(hP W hp).1,Finset.mem_singleton.mpr (hP W hp).2⟩)
  simp only [Finset.card_singleton,Nat.cast_one,one_mul] at hh
  convert hh using 1
  all_goals
    apply Finset.sum_congr
    · ext W;simp
    · intro W _;split_ifs <;> rfl

theorem ordinary_wheel_free_hub_event (hu : Fintype.card U≤Fintype.card V)
    (S : Finset V) (hS : 2≤S.card) (P : OrdinaryWheel Q F H r → Prop)
    (hP : ∀ W,P W → (↑S:Set V)⊆(ordinaryWheelRim W).support) :
    (∑ W,if P W then w W else 0)≤(r:ℝ)^S.card*B/(Fintype.card V:ℝ)^(S.card-2) := by
  have hh := ordinary_wheel_event_weight_bound Q F H r hr hn w B hB hw S hS Finset.univ P
    (by intro W hp;exact ⟨hP W hp,Finset.mem_univ _⟩)
  simp only [Finset.card_univ] at hh
  have hn0 : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  apply hh.trans
  calc
    _ ≤ (Fintype.card V:ℝ)*(r:ℝ)^S.card*B/(Fintype.card V:ℝ)^(S.card-1) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hB
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hu
    _ = _ := by
      have hp : (Fintype.card V:ℝ)^(S.card-1)=(Fintype.card V:ℝ)^(S.card-2)*Fintype.card V := by
        rw [← pow_succ,show S.card-2+1=S.card-1 by omega]
      rw [hp]
      field_simp

theorem ordinary_wheel_rim_spoke_pair (x y : V) (hxy : x≠y) (z : V) (u : U) :
    (∑ W,if (ordinaryWheelRim W).Adj x y ∧ ordinaryWheelHub W=u ∧ z∈(ordinaryWheelRim W).support
      then w W else 0)≤(r:ℝ)^2*B/Fintype.card V := by
  have hc : ({x,y}:Finset V).card=2 := by simp [hxy]
  have hh := ordinary_wheel_fixed_hub_event Q F H r hr hn w B hB hw {x,y} (by rw [hc]) u
    (fun W=>(ordinaryWheelRim W).Adj x y ∧ ordinaryWheelHub W=u ∧ z∈(ordinaryWheelRim W).support)
    (by
      intro W h
      refine ⟨?_,h.2.1⟩
      intro v hv
      simp only [Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] at hv
      rcases hv with rfl|rfl
      · exact h.1.mem_support_left
      · exact h.1.mem_support_right)
  simp only [hc,show 2-1=1 from rfl,pow_one] at hh
  convert hh using 1
  all_goals
    apply Finset.sum_congr
    · ext W;simp
    · intro W _;split_ifs <;> rfl

theorem ordinary_wheel_spoke_pair (x y : V) (hxy : x≠y) (u : U) :
    (∑ W,if ordinaryWheelHub W=u ∧ x∈(ordinaryWheelRim W).support ∧ y∈(ordinaryWheelRim W).support
      then w W else 0)≤(r:ℝ)^2*B/Fintype.card V := by
  have hc : ({x,y}:Finset V).card=2 := by simp [hxy]
  have hh := ordinary_wheel_fixed_hub_event Q F H r hr hn w B hB hw {x,y} (by rw [hc]) u
    (fun W=>ordinaryWheelHub W=u ∧ x∈(ordinaryWheelRim W).support ∧ y∈(ordinaryWheelRim W).support)
    (by
      intro W h
      refine ⟨?_,h.1⟩
      intro v hv
      simp only [Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] at hv
      rcases hv with rfl|rfl
      · exact h.2.1
      · exact h.2.2)
  simp only [hc,show 2-1=1 from rfl,pow_one] at hh
  convert hh using 1
  all_goals
    apply Finset.sum_congr
    · ext W;simp
    · intro W _;split_ifs <;> rfl

theorem ordinary_wheel_adjacent_rim_pair (hu : Fintype.card U≤Fintype.card V)
    (x y z : V) (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) :
    (∑ W,if (ordinaryWheelRim W).Adj x y ∧ (ordinaryWheelRim W).Adj x z then w W else 0)≤
      (r:ℝ)^3*B/Fintype.card V := by
  have hc : ({x,y,z}:Finset V).card=3 := by simp [hxy,hxz,hyz]
  have hh := ordinary_wheel_free_hub_event Q F H r hr hn w B hB hw hu {x,y,z} (by rw [hc];omega)
    (fun W=>(ordinaryWheelRim W).Adj x y ∧ (ordinaryWheelRim W).Adj x z)
    (by
      intro W h v hv
      simp only [Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] at hv
      rcases hv with rfl|rfl|rfl
      · exact h.1.mem_support_left
      · exact h.1.mem_support_right
      · exact h.2.mem_support_right)
  simp only [hc,show 3-2=1 from rfl,pow_one] at hh
  convert hh using 1
  all_goals
    apply Finset.sum_congr
    · ext W;simp
    · intro W _;split_ifs <;> rfl

theorem ordinary_wheel_disjoint_rim_pair (hu : Fintype.card U≤Fintype.card V)
    (x y z t : V) (hxy : x≠y) (hxz : x≠z) (hxt : x≠t) (hyz : y≠z) (hyt : y≠t) (hzt : z≠t) :
    (∑ W,if (ordinaryWheelRim W).Adj x y ∧ (ordinaryWheelRim W).Adj z t then w W else 0)≤
      (r:ℝ)^4*B/(Fintype.card V:ℝ)^2 := by
  have hc : ({x,y,z,t}:Finset V).card=4 := by simp [hxy,hxz,hxt,hyz,hyt,hzt]
  have hh := ordinary_wheel_free_hub_event Q F H r hr hn w B hB hw hu {x,y,z,t} (by rw [hc];omega)
    (fun W=>(ordinaryWheelRim W).Adj x y ∧ (ordinaryWheelRim W).Adj z t)
    (by
      intro W h v hv
      simp only [Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] at hv
      rcases hv with rfl|rfl|rfl|rfl
      · exact h.1.mem_support_left
      · exact h.1.mem_support_right
      · exact h.2.mem_support_left
      · exact h.2.mem_support_right)
  simp only [hc,show 4-2=2 from rfl] at hh
  convert hh using 1
  all_goals
    apply Finset.sum_congr
    · ext W;simp
    · intro W _;split_ifs <;> rfl

theorem ordinary_wheel_rim_spoke_offroot (x y z : V) (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) (u : U) :
    (∑ W,if (ordinaryWheelRim W).Adj x y ∧ ordinaryWheelHub W=u ∧ z∈(ordinaryWheelRim W).support
      then w W else 0)≤(r:ℝ)^3*B/(Fintype.card V:ℝ)^2 := by
  have hc : ({x,y,z}:Finset V).card=3 := by simp [hxy,hxz,hyz]
  have hh := ordinary_wheel_fixed_hub_event Q F H r hr hn w B hB hw {x,y,z} (by rw [hc];omega) u
    (fun W=>(ordinaryWheelRim W).Adj x y ∧ ordinaryWheelHub W=u ∧ z∈(ordinaryWheelRim W).support)
    (by
      intro W h
      refine ⟨?_,h.2.1⟩
      intro v hv
      simp only [Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] at hv
      rcases hv with rfl|rfl|rfl
      · exact h.1.mem_support_left
      · exact h.1.mem_support_right
      · exact h.2.2)
  simp only [hc,show 3-1=2 from rfl] at hh
  convert hh using 1
  all_goals
    apply Finset.sum_congr
    · ext W;simp
    · intro W _;split_ifs <;> rfl

end Oberwolfach
