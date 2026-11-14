module

public import Oberwolfach.MarkedSeparatedPairLoads

@[expose] public section

/-! Root-omitted pair costs for summing realized sparse deletions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E K : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
  {H₀ Hₖ : V → U → Prop}

def markedRimPairWeight (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (e f : E⊕K) : ℝ :=
  ∑ W,if markedPhysicalEdge tail head ktail khead π e∈markedCyclePhysicalEdges tail head ktail khead m π b W.1 ∧
    markedPhysicalEdge tail head ktail khead π f∈markedCyclePhysicalEdges tail head ktail khead m π b W.1 then w W else 0

def markedRimSpokePairWeight (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ)
    (e : E⊕K) (v : V) (u : U) : ℝ :=
  ∑ W,if markedPhysicalEdge tail head ktail khead π e∈markedCyclePhysicalEdges tail head ktail khead m π b W.1 ∧
    (W.2.val=u ∧ v∈Set.range W.1.val) then w W else 0

def markedSpokePairWeight (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ)
    (v x : V) (u t : U) : ℝ :=
  ∑ W,if (W.2.val=u ∧ v∈Set.range W.1.val) ∧ (W.2.val=t ∧ x∈Set.range W.1.val) then w W else 0

theorem marked_rim_rim_pair_cost (hm : 3≤m)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,w W≤B/(Fintype.card V:ℝ)^m) (e f : E⊕K) :
    (if e=f then 0 else markedRimPairWeight w e f)≤
      if Sum.elim tail ktail f∈({Sum.elim tail ktail e,Sum.elim head khead e}:Finset V) ∨
        Sum.elim head khead f∈({Sum.elim tail ktail e,Sum.elim head khead e}:Finset V)
      then ((m:ℝ)+1)^4*B/Fintype.card V else ((m:ℝ)+1)^4*B/(Fintype.card V:ℝ)^2 := by
  by_cases hef : e=f
  · simp only [hef,ite_true]
    split_ifs <;> positivity
  · rw [if_neg hef]
    split_ifs with hmeet
    · exact marked_wheel_distinct_rim_pair hm hp hn hu w B hB hw e f hef
    · apply marked_wheel_disjoint_rim_pair hm hp hn hu w B hB hw e f
      apply Finset.disjoint_right.mpr
      intro v hv he
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl|rfl
      · exact hmeet (Or.inl he)
      · exact hmeet (Or.inr he)

theorem marked_rim_spoke_pair_cost (hm : 3≤m)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hn : 0<Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,w W≤B/(Fintype.card V:ℝ)^m) (e : E⊕K) (v : V) (u : U) :
    markedRimSpokePairWeight w e v u≤
      if v∈({Sum.elim tail ktail e,Sum.elim head khead e}:Finset V)
      then ((m:ℝ)+1)^4*B/Fintype.card V else ((m:ℝ)+1)^4*B/(Fintype.card V:ℝ)^2 := by
  have hc : (1:ℝ)≤m+1 := by linarith [(Nat.cast_nonneg m : (0:ℝ)≤m)]
  split_ifs with hv
  · apply (marked_wheel_rim_spoke_pair (by omega) hp hn w B hB hw e v u).trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc (by omega : 2≤4)) hB) (Nat.cast_nonneg _)
  · apply (marked_wheel_nonincident_rim_spoke_pair (by omega) hp hn w B hB hw e v u hv).trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc (by omega : 3≤4)) hB) (sq_nonneg _)

theorem marked_spoke_rim_pair_cost (hm : 3≤m)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hn : 0<Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,w W≤B/(Fintype.card V:ℝ)^m) (e : E⊕K) (v : V) (u : U) :
    markedRimSpokePairWeight w e v u≤
      if Sum.elim tail ktail e=v ∨ Sum.elim head khead e=v
      then ((m:ℝ)+1)^4*B/Fintype.card V else ((m:ℝ)+1)^4*B/(Fintype.card V:ℝ)^2 := by
  simpa only [Finset.mem_insert,Finset.mem_singleton,eq_comm] using
    marked_rim_spoke_pair_cost hm hp hn w B hB hw e v u

theorem marked_spoke_spoke_pair_cost (hm : 3≤m) (hn : 0<Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,w W≤B/(Fintype.card V:ℝ)^m) (v x : V) (u t : U) :
    (if (v,u)=(x,t) then 0 else markedSpokePairWeight w v x u t)≤
      if t=u then ((m:ℝ)+1)^4*B/Fintype.card V else 0 := by
  by_cases hut : t=u
  · subst t
    rw [if_pos rfl]
    by_cases hvx : v=x
    · simp only [hvx,ite_true]
      positivity
    · have hne : (v,u)≠(x,u) := fun he=>hvx (congrArg Prod.fst he)
      rw [if_neg hne]
      have hh := marked_wheel_spoke_pair (by omega) hn w B hB hw v x hvx u
      have he : markedSpokePairWeight w v x u u=
          ∑ W,if W.2.val=u ∧ v∈Set.range W.1.val ∧ x∈Set.range W.1.val then w W else 0 := by
        unfold markedSpokePairWeight
        apply Finset.sum_congr rfl
        intro W _
        simp only [and_assoc,and_left_comm,and_self_left]
      rw [he]
      apply hh.trans
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg m : (0:ℝ)≤m)] : (1:ℝ)≤m+1) (by omega : 2≤4)) hB)
        (Nat.cast_nonneg _)
  · rw [if_neg hut]
    have hne : (v,u)≠(x,t) := fun he=>hut (congrArg Prod.snd he).symm
    rw [if_neg hne]
    unfold markedSpokePairWeight
    have hfalse (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :
        ¬((W.2.val=u ∧ v∈Set.range W.1.val) ∧ (W.2.val=t ∧ x∈Set.range W.1.val)) :=
      fun h=>hut (h.2.1.symm.trans h.1.1)
    simp only [hfalse,ite_false,Finset.sum_const_zero,le_refl]

end Oberwolfach
