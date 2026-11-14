module

public import Oberwolfach.OrdinaryWheelPairLoads

@[expose] public section

/-! The physical wheel hypergraph has weighted codegree O(1/n). This
compares distinct physical edges and counts each actual wheel once. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem uniform_wheel_pair_scale (n R B : ℝ) (hn : 1≤n) (hR : 1≤R) (hB : 0≤B)
    (s a : ℕ) (hs : s≤4) (ha : 1≤a) : R^s*B/n^a≤R^4*B/n := by
  have hn0 : 0<n := lt_of_lt_of_le zero_lt_one hn
  have hpow : R^s≤R^4 := pow_le_pow_right₀ hR hs
  have hnp : n≤n^a := by simpa only [pow_one] using pow_le_pow_right₀ hn ha
  calc
    _ ≤ R^4*B/n^a := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hB) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hn0 hnp

theorem distinct_pair_union_card {V : Type*} [DecidableEq V]
    (x y z t : V) (hxy : x≠y) (hzt : z≠t) (he : s(x,y)≠s(z,t)) :
    3≤({x,y,z,t}:Finset V).card ∧ ({x,y,z,t}:Finset V).card≤4 := by
  constructor
  · have hthree (v : V) (hxv : x≠v) (hyv : y≠v) (hv : v∈({z,t}:Finset V)) :
        3≤({x,y,z,t}:Finset V).card := by
      have hs : ({x,y,v}:Finset V)⊆{x,y,z,t} := by
        intro a ha
        simp only [Finset.mem_insert,Finset.mem_singleton] at ha hv ⊢
        rcases ha with rfl | rfl | rfl <;> tauto
      have hc : ({x,y,v}:Finset V).card=3 := by simp [hxy,hxv,hyv]
      rw [← hc]
      exact Finset.card_le_card hs
    by_cases hz : z=x ∨ z=y
    · by_cases ht : t=x ∨ t=y
      · exfalso
        rcases hz with rfl|rfl <;> rcases ht with rfl|rfl
        · exact hzt rfl
        · exact he rfl
        · exact he (Sym2.eq_swap)
        · exact hzt rfl
      · apply hthree t (by tauto) (by tauto) (by simp)
    · apply hthree z (by tauto) (by tauto) (by simp)
  · have h1 := Finset.card_insert_le x ({y,z,t}:Finset V)
    have h2 := Finset.card_insert_le y ({z,t}:Finset V)
    have h3 := Finset.card_insert_le z ({t}:Finset V)
    have h4 : ({t}:Finset V).card=1 := Finset.card_singleton _
    omega

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (Q F : SimpleGraph V) (H : V → U → Prop) (r : ℕ) (hr : 2≤r) (hn : 0<Fintype.card V)
    (hu : Fintype.card U≤Fintype.card V)
    (w : OrdinaryWheel Q F H r → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^(r-1))
include hr hn hu hB hw

theorem ordinary_wheel_distinct_rim_pair (x y z t : V) (hxy : x≠y) (hzt : z≠t)
    (he : s(x,y)≠s(z,t)) :
    (∑ W,if (ordinaryWheelRim W).Adj x y ∧ (ordinaryWheelRim W).Adj z t then w W else 0)≤
      (r:ℝ)^4*B/Fintype.card V := by
  obtain ⟨hlo,hhi⟩ := distinct_pair_union_card x y z t hxy hzt he
  have hh := ordinary_wheel_free_hub_event Q F H r hr hn w B hB hw hu {x,y,z,t} (by omega)
    (fun W=>(ordinaryWheelRim W).Adj x y ∧ (ordinaryWheelRim W).Adj z t)
    (by
      intro W h v hv
      simp only [Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] at hv
      rcases hv with rfl|rfl|rfl|rfl
      · exact h.1.mem_support_left
      · exact h.1.mem_support_right
      · exact h.2.mem_support_left
      · exact h.2.mem_support_right)
  have hb := uniform_wheel_pair_scale (Fintype.card V:ℝ) (r:ℝ) B
    (by exact_mod_cast (show 1≤Fintype.card V by omega))
    (by exact_mod_cast (show 1≤r by omega)) hB
    ({x,y,z,t}:Finset V).card (({x,y,z,t}:Finset V).card-2) hhi (by omega)
  have ht := hh.trans hb
  convert ht using 1
  apply Finset.sum_congr
  · ext W;simp
  · intro W _;split_ifs <;> rfl

end Oberwolfach
