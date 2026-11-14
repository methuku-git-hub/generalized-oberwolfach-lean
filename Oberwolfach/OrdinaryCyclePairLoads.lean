module

public import Oberwolfach.OrdinaryCycleRootCounts
public import Oberwolfach.OrdinaryCycleIncidence
public import Oberwolfach.TransversalWeightBounds

@[expose] public section

/-! Pair-load estimates for the positive bounded ordinary cycle weights.
They count physical cycle subgraphs, with no embedding multiplicity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_cycle_event_weight_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) (hr : 0<r) (hn : 0<Fintype.card V)
    (a : OrdinaryCycle G r → ℝ) (ha : ∀ C,0≤a C)
    (B : ℝ) (hB : 0≤B) (hb : ∀ C,a C≤B/(Fintype.card V:ℝ)^(r-2))
    (S : Finset V) (hS : 2≤S.card) (E : OrdinaryCycle G r → Prop)
    (hE : ∀ C,E C → (↑S:Set V)⊆C.val.val.support) :
    (∑ C,if E C then a C else 0)≤(r:ℝ)^S.card*B/(Fintype.card V:ℝ)^(S.card-2) := by
  have hn' : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hM : 0≤B/(Fintype.card V:ℝ)^(r-2) := by positivity
  by_cases hSr : S.card≤r
  · calc
      _ ≤ ∑ C : OrdinaryCycle G r,if (↑S:Set V)⊆C.val.val.support then B/(Fintype.card V:ℝ)^(r-2) else 0 := by
        apply Finset.sum_le_sum
        intro C _
        by_cases h : E C
        · rw [if_pos h,if_pos (hE C h)]
          exact hb C
        · rw [if_neg h]
          split_ifs
          · exact hM
          · exact le_refl _
      _ = (∑ C : OrdinaryCycle G r,if (↑S:Set V)⊆C.val.val.support then (1:ℝ) else 0)*
          (B/(Fintype.card V:ℝ)^(r-2)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro C _
        split_ifs <;> simp
      _ ≤ (∑ C : EmbeddedCycleFamily V r,if (↑S:Set V)⊆C.val.support then (1:ℝ) else 0)*
          (B/(Fintype.card V:ℝ)^(r-2)) := by
        apply mul_le_mul_of_nonneg_right _ hM
        exact finite_subtype_sum_le (fun C : EmbeddedCycleFamily V r => C.val≤G)
          (fun C => if (↑S:Set V)⊆C.val.support then (1:ℝ) else 0) (fun C => by split_ifs <;> norm_num)
      _ ≤ ((r:ℝ)^S.card*(Fintype.card V:ℝ)^(r-S.card))*
          (B/(Fintype.card V:ℝ)^(r-2)) :=
        mul_le_mul_of_nonneg_right (ordinary_cycle_root_count r hr S) hM
      _ = _ := by
        rw [mul_assoc,normalized_transversal_power _ _ _ _ hn'.ne' hS hSr]
        ring
  · have hfalse (C : OrdinaryCycle G r) : ¬E C := by
      intro hc
      have hsub : S⊆C.val.val.support.toFinset := by
        intro v hv
        exact Set.mem_toFinset.mpr (hE C hc hv)
      have hh := Finset.card_le_card hsub
      rw [C.val.property.support_card] at hh
      exact hSr hh
    simp only [hfalse,ite_false,Finset.sum_const_zero]
    positivity

theorem ordinary_cycle_adjacent_pair_load {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) (hr : 0<r) (hn : 0<Fintype.card V)
    (a : OrdinaryCycle G r → ℝ) (ha : ∀ C,0≤a C)
    (B : ℝ) (hB : 0≤B) (hb : ∀ C,a C≤B/(Fintype.card V:ℝ)^(r-2))
    (x y z : V) (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) :
    (∑ C,if C.val.val.Adj x y ∧ C.val.val.Adj x z then a C else 0)≤
      (r:ℝ)^3*B/Fintype.card V := by
  have hc : ({x,y,z}:Finset V).card=3 := by simp [hxy,hxz,hyz]
  have hh := ordinary_cycle_event_weight_bound G r hr hn a ha B hB hb {x,y,z}
    (by rw [hc];norm_num) (fun C => C.val.val.Adj x y ∧ C.val.val.Adj x z) (by
      intro C h v hv
      simp only [Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] at hv
      rcases hv with rfl|rfl|rfl
      · exact h.1.mem_support_left
      · exact h.1.mem_support_right
      · exact h.2.mem_support_right)
  simp only [hc,show 3-2=1 from rfl,pow_one] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro C _
  split_ifs <;> rfl

theorem ordinary_cycle_disjoint_pair_load {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) (hr : 0<r) (hn : 0<Fintype.card V)
    (a : OrdinaryCycle G r → ℝ) (ha : ∀ C,0≤a C)
    (B : ℝ) (hB : 0≤B) (hb : ∀ C,a C≤B/(Fintype.card V:ℝ)^(r-2))
    (x y z t : V) (hxy : x≠y) (hxz : x≠z) (hxt : x≠t)
    (hyz : y≠z) (hyt : y≠t) (hzt : z≠t) :
    (∑ C,if C.val.val.Adj x y ∧ C.val.val.Adj z t then a C else 0)≤
      (r:ℝ)^4*B/(Fintype.card V:ℝ)^2 := by
  have hc : ({x,y,z,t}:Finset V).card=4 := by simp [hxy,hxz,hxt,hyz,hyt,hzt]
  have hh := ordinary_cycle_event_weight_bound G r hr hn a ha B hB hb {x,y,z,t}
    (by rw [hc];norm_num) (fun C => C.val.val.Adj x y ∧ C.val.val.Adj z t) (by
      intro C h v hv
      simp only [Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] at hv
      rcases hv with rfl|rfl|rfl|rfl
      · exact h.1.mem_support_left
      · exact h.1.mem_support_right
      · exact h.2.mem_support_left
      · exact h.2.mem_support_right)
  simp only [hc,show 4-2=2 from rfl] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro C _
  split_ifs <;> rfl

end Oberwolfach
