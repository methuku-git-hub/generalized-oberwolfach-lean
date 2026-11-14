module

public import Oberwolfach.MarkedWheelPairLoads

@[expose] public section

/-! Stronger pair-load bounds when an extra resource fixes new auxiliary
vertices. These are used with actual deletion degrees, not densities. -/
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

theorem marked_wheel_disjoint_rim_pair (hm : 3≤m)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,w W≤B/(Fintype.card V:ℝ)^m) (e f : E⊕K)
    (hdisj : Disjoint ({Sum.elim tail ktail e,Sum.elim head khead e}:Finset V)
      {Sum.elim tail ktail f,Sum.elim head khead f}) :
    (∑ W,if markedPhysicalEdge tail head ktail khead π e∈markedCyclePhysicalEdges tail head ktail khead m π b W.1 ∧
      markedPhysicalEdge tail head ktail khead π f∈markedCyclePhysicalEdges tail head ktail khead m π b W.1 then w W else 0)≤
      ((m:ℝ)+1)^4*B/(Fintype.card V:ℝ)^2 := by
  let P (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :=
    markedPhysicalEdge tail head ktail khead π e∈markedCyclePhysicalEdges tail head ktail khead m π b W.1 ∧
    markedPhysicalEdge tail head ktail khead π f∈markedCyclePhysicalEdges tail head ktail khead m π b W.1
  change (∑ W,if P W then w W else 0)≤_
  by_cases hex : ∃ W,P W
  · obtain ⟨W,hW⟩ := hex
    have he := marked_cycle_arc_nonloop (by omega) hp W.1 e hW.1
    have hf := marked_cycle_arc_nonloop (by omega) hp W.1 f hW.2
    let S : Finset V := {Sum.elim tail ktail e,Sum.elim head khead e} ∪
      {Sum.elim tail ktail f,Sum.elim head khead f}
    have hS : S.card=4 := by dsimp [S];rw [Finset.card_union_of_disjoint hdisj];simp [he,hf]
    have hbound := marked_wheel_free_hub_event hn hu w B hB hw S (by omega) (by omega) P
      (by
        intro Z hZ v hv
        have he := marked_cycle_arc_endpoints_present hp Z.1 e hZ.1
        have hf := marked_cycle_arc_endpoints_present hp Z.1 f hZ.2
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

theorem marked_wheel_nonincident_rim_spoke_pair (hm : 2≤m)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hn : 0<Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,w W≤B/(Fintype.card V:ℝ)^m) (e : E⊕K) (v : V) (u : U)
    (hv : v∉({Sum.elim tail ktail e,Sum.elim head khead e}:Finset V)) :
    (∑ W,if markedPhysicalEdge tail head ktail khead π e∈markedCyclePhysicalEdges tail head ktail khead m π b W.1 ∧
      (W.2.val=u ∧ v∈Set.range W.1.val) then w W else 0)≤
      ((m:ℝ)+1)^3*B/(Fintype.card V:ℝ)^2 := by
  let P (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :=
    markedPhysicalEdge tail head ktail khead π e∈markedCyclePhysicalEdges tail head ktail khead m π b W.1 ∧
      (W.2.val=u ∧ v∈Set.range W.1.val)
  change (∑ W,if P W then w W else 0)≤_
  by_cases hex : ∃ W,P W
  · obtain ⟨W,hW⟩ := hex
    have he := marked_cycle_arc_nonloop (by omega) hp W.1 e hW.1
    let S : Finset V := insert v {Sum.elim tail ktail e,Sum.elim head khead e}
    have hS : S.card=3 := by dsimp [S];rw [Finset.card_insert_of_notMem hv];simp [he]
    have hbound := marked_wheel_fixed_hub_event hn w B hB hw S (by omega) (by omega) u P
      (by
        intro Z hZ
        refine ⟨?_,hZ.2.1⟩
        intro z hz
        have he := marked_cycle_arc_endpoints_present hp Z.1 e hZ.1
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
