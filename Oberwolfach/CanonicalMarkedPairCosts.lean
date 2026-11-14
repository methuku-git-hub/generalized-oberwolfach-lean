module

public import Oberwolfach.CanonicalMarkedPairBounds
public import Oberwolfach.MarkedPairCosts

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

def canonicalMarkedRimPairWeight (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (e f : E⊕K) : ℝ :=
  ∑ W,if CanonicalMarkedArcMem W.1 e ∧
    CanonicalMarkedArcMem W.1 f then w W else 0

def canonicalMarkedRimSpokePairWeight (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ)
    (e : E⊕K) (v : V) (u : U) : ℝ :=
  ∑ W,if CanonicalMarkedArcMem W.1 e ∧
    (W.2.val=u ∧ v∈Set.range W.1.val) then w W else 0

theorem canonical_marked_rim_rim_pair_cost (hm : 3≤m)
    (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,w W≤B/(Fintype.card V:ℝ)^m) (e f : E⊕K) :
    (if e=f then 0 else canonicalMarkedRimPairWeight w e f)≤
      if Sum.elim tail ktail f∈({Sum.elim tail ktail e,Sum.elim head khead e}:Finset V) ∨
        Sum.elim head khead f∈({Sum.elim tail ktail e,Sum.elim head khead e}:Finset V)
      then ((m:ℝ)+1)^4*B/Fintype.card V else ((m:ℝ)+1)^4*B/(Fintype.card V:ℝ)^2 := by
  by_cases hef : e=f
  · simp only [hef,ite_true]
    split_ifs <;> positivity
  · rw [if_neg hef]
    split_ifs with hmeet
    · exact canonical_marked_wheel_distinct_rim_pair hm hn hu w B hB hw e f hef
    · apply canonical_marked_wheel_disjoint_rim_pair hm hn hu w B hB hw e f
      apply Finset.disjoint_right.mpr
      intro v hv he
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl|rfl
      · exact hmeet (Or.inl he)
      · exact hmeet (Or.inr he)

theorem canonical_marked_rim_spoke_pair_cost (hm : 3≤m)
    (hn : 0<Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,w W≤B/(Fintype.card V:ℝ)^m) (e : E⊕K) (v : V) (u : U) :
    canonicalMarkedRimSpokePairWeight w e v u≤
      if v∈({Sum.elim tail ktail e,Sum.elim head khead e}:Finset V)
      then ((m:ℝ)+1)^4*B/Fintype.card V else ((m:ℝ)+1)^4*B/(Fintype.card V:ℝ)^2 := by
  have hc : (1:ℝ)≤m+1 := by linarith [(Nat.cast_nonneg m : (0:ℝ)≤m)]
  split_ifs with hv
  · apply (canonical_marked_wheel_rim_spoke_pair (by omega) hn w B hB hw e v u).trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc (by omega : 2≤4)) hB) (Nat.cast_nonneg _)
  · apply (canonical_marked_wheel_nonincident_rim_spoke_pair (by omega) hn w B hB hw e v u hv).trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc (by omega : 3≤4)) hB) (sq_nonneg _)

theorem canonical_marked_spoke_rim_pair_cost (hm : 3≤m)
    (hn : 0<Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,w W≤B/(Fintype.card V:ℝ)^m) (e : E⊕K) (v : V) (u : U) :
    canonicalMarkedRimSpokePairWeight w e v u≤
      if Sum.elim tail ktail e=v ∨ Sum.elim head khead e=v
      then ((m:ℝ)+1)^4*B/Fintype.card V else ((m:ℝ)+1)^4*B/(Fintype.card V:ℝ)^2 := by
  simpa only [Finset.mem_insert,Finset.mem_singleton,eq_comm] using
    canonical_marked_rim_spoke_pair_cost hm hn w B hB hw e v u


end Oberwolfach
