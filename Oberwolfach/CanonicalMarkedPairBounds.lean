module

public import Oberwolfach.CanonicalMarkedArcMembership
public import Oberwolfach.MarkedWheelPairLoads
public import Oberwolfach.MarkedWheelEventScales

@[expose] public section

/-! Pair estimates for typed arcs in the full fixed candidate universe.
Different potential arcs may have the same physical image. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E K : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
  {H₀ Hₖ : V → U → Prop}

theorem canonical_marked_wheel_distinct_rim_pair (hm : 3≤m)
    (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,w W≤B/(Fintype.card V:ℝ)^m) (e f : E⊕K) (hef : e≠f) :
    (∑ W,if CanonicalMarkedArcMem W.1 e ∧
      CanonicalMarkedArcMem W.1 f then w W else 0)≤
      ((m:ℝ)+1)^4*B/Fintype.card V := by
  let P (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :=
    CanonicalMarkedArcMem W.1 e ∧
    CanonicalMarkedArcMem W.1 f
  change (∑ W,if P W then w W else 0)≤_
  by_cases hex : ∃ W,P W
  · obtain ⟨W,hW⟩ := hex
    let S : Finset V := {Sum.elim tail ktail e,Sum.elim head khead e,Sum.elim tail ktail f,Sum.elim head khead f}
    have hS : 3≤S.card := canonicalMarkedArc_pair_root_card (by omega) W.1 e f hef hW.1 hW.2
    have hS4 : S.card≤4 := by
      dsimp [S]
      have h1 := Finset.card_insert_le (Sum.elim tail ktail e)
        ({Sum.elim head khead e,Sum.elim tail ktail f,Sum.elim head khead f}:Finset V)
      have h2 := Finset.card_insert_le (Sum.elim head khead e)
        ({Sum.elim tail ktail f,Sum.elim head khead f}:Finset V)
      have h3 := Finset.card_insert_le (Sum.elim tail ktail f) ({Sum.elim head khead f}:Finset V)
      simp only [Finset.card_singleton] at h3
      omega
    have hbound := marked_wheel_free_hub_event hn hu w B hB hw S (by omega) (by omega) P
      (by
        intro Z hZ v hv
        have he := canonicalMarkedArc_endpoints_present Z.1 e hZ.1
        have hf := canonicalMarkedArc_endpoints_present Z.1 f hZ.2
        simp only [S,Finset.mem_insert,Finset.mem_singleton] at hv
        rcases hv with rfl|rfl|rfl|rfl
        · exact he.1
        · exact he.2
        · exact hf.1
        · exact hf.2)
    have ht := hbound.trans (uniform_wheel_pair_scale _ _ B
      (by exact_mod_cast (show 1≤Fintype.card V by omega))
      (by linarith [show (0:ℝ)≤m from Nat.cast_nonneg m]) hB S.card (S.card-2) hS4 (by omega))
    convert ht using 1
    apply Finset.sum_congr rfl
    intro Z _
    by_cases h : P Z <;> simp only [h,ite_true,ite_false]
  · have hfalse : ∀ W,¬P W := by simpa only [not_exists] using hex
    simp only [hfalse,ite_false,Finset.sum_const_zero]
    positivity

theorem canonical_marked_wheel_rim_spoke_pair (hm : 1≤m)
    (hn : 0<Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,w W≤B/(Fintype.card V:ℝ)^m) (e : E⊕K) (v : V) (u : U) :
    (∑ W,if CanonicalMarkedArcMem W.1 e ∧
      (W.2.val=u ∧ v∈Set.range W.1.val) then w W else 0)≤
      ((m:ℝ)+1)^2*B/Fintype.card V := by
  let P (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :=
    CanonicalMarkedArcMem W.1 e ∧
      (W.2.val=u ∧ v∈Set.range W.1.val)
  change (∑ W,if P W then w W else 0)≤_
  by_cases hex : ∃ W,P W
  · obtain ⟨W,hW⟩ := hex
    have hne := canonicalMarkedArc_nonloop hm W.1 e hW.1
    let S : Finset V := {Sum.elim tail ktail e,Sum.elim head khead e}
    have hS : S.card=2 := by simp [S,hne]
    have hbound := marked_wheel_fixed_hub_event hn w B hB hw S (by omega) (by omega) u P
      (by
        intro Z hZ
        refine ⟨?_,hZ.2.1⟩
        intro z hz
        have he := canonicalMarkedArc_endpoints_present Z.1 e hZ.1
        simp only [S,Finset.mem_insert,Finset.mem_singleton] at hz
        rcases hz with rfl|rfl
        · exact he.1
        · exact he.2)
    simp only [hS,show 2-1=1 from rfl,pow_one] at hbound
    convert hbound using 1
    apply Finset.sum_congr rfl
    intro Z _
    by_cases h : P Z <;> simp only [h,ite_true,ite_false]
  · have hfalse : ∀ W,¬P W := by simpa only [not_exists] using hex
    simp only [hfalse,ite_false,Finset.sum_const_zero]
    positivity

theorem canonical_marked_wheel_disjoint_rim_pair (hm : 3≤m)
    (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,w W≤B/(Fintype.card V:ℝ)^m) (e f : E⊕K)
    (hdisj : Disjoint ({Sum.elim tail ktail e,Sum.elim head khead e}:Finset V)
      {Sum.elim tail ktail f,Sum.elim head khead f}) :
    (∑ W,if CanonicalMarkedArcMem W.1 e ∧
      CanonicalMarkedArcMem W.1 f then w W else 0)≤
      ((m:ℝ)+1)^4*B/(Fintype.card V:ℝ)^2 := by
  let P (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :=
    CanonicalMarkedArcMem W.1 e ∧
    CanonicalMarkedArcMem W.1 f
  change (∑ W,if P W then w W else 0)≤_
  by_cases hex : ∃ W,P W
  · obtain ⟨W,hW⟩ := hex
    have he := canonicalMarkedArc_nonloop (by omega) W.1 e hW.1
    have hf := canonicalMarkedArc_nonloop (by omega) W.1 f hW.2
    let S : Finset V := {Sum.elim tail ktail e,Sum.elim head khead e} ∪
      {Sum.elim tail ktail f,Sum.elim head khead f}
    have hS : S.card=4 := by dsimp [S];rw [Finset.card_union_of_disjoint hdisj];simp [he,hf]
    have hbound := marked_wheel_free_hub_event hn hu w B hB hw S (by omega) (by omega) P
      (by
        intro Z hZ v hv
        have he := canonicalMarkedArc_endpoints_present Z.1 e hZ.1
        have hf := canonicalMarkedArc_endpoints_present Z.1 f hZ.2
        simp only [S,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hv
        rcases hv with (rfl|rfl)|(rfl|rfl)
        · exact he.1
        · exact he.2
        · exact hf.1
        · exact hf.2)
    simp only [hS,show 4-2=2 from rfl] at hbound
    convert hbound using 1
    apply Finset.sum_congr rfl
    intro Z _
    by_cases h : P Z <;> simp only [h,ite_true,ite_false]
  · have hfalse : ∀ W,¬P W := by simpa only [not_exists] using hex
    simp only [hfalse,ite_false,Finset.sum_const_zero]
    positivity

theorem canonical_marked_wheel_nonincident_rim_spoke_pair (hm : 2≤m)
    (hn : 0<Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,w W≤B/(Fintype.card V:ℝ)^m) (e : E⊕K) (v : V) (u : U)
    (hv : v∉({Sum.elim tail ktail e,Sum.elim head khead e}:Finset V)) :
    (∑ W,if CanonicalMarkedArcMem W.1 e ∧
      (W.2.val=u ∧ v∈Set.range W.1.val) then w W else 0)≤
      ((m:ℝ)+1)^3*B/(Fintype.card V:ℝ)^2 := by
  let P (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :=
    CanonicalMarkedArcMem W.1 e ∧
      (W.2.val=u ∧ v∈Set.range W.1.val)
  change (∑ W,if P W then w W else 0)≤_
  by_cases hex : ∃ W,P W
  · obtain ⟨W,hW⟩ := hex
    have he := canonicalMarkedArc_nonloop (by omega) W.1 e hW.1
    let S : Finset V := insert v {Sum.elim tail ktail e,Sum.elim head khead e}
    have hS : S.card=3 := by dsimp [S];rw [Finset.card_insert_of_notMem hv];simp [he]
    have hbound := marked_wheel_fixed_hub_event hn w B hB hw S (by omega) (by omega) u P
      (by
        intro Z hZ
        refine ⟨?_,hZ.2.1⟩
        intro z hz
        have he := canonicalMarkedArc_endpoints_present Z.1 e hZ.1
        simp only [S,Finset.mem_insert,Finset.mem_singleton] at hz
        rcases hz with rfl|rfl|rfl
        · exact hZ.2.2
        · exact he.1
        · exact he.2)
    simp only [hS,show 3-1=2 from rfl] at hbound
    convert hbound using 1
    apply Finset.sum_congr rfl
    intro Z _
    by_cases h : P Z <;> simp only [h,ite_true,ite_false]
  · have hfalse : ∀ W,¬P W := by simpa only [not_exists] using hex
    simp only [hfalse,ite_false,Finset.sum_const_zero]
    positivity

end Oberwolfach
