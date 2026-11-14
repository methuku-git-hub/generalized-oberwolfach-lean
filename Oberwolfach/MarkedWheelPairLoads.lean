module

public import Oberwolfach.MarkedArcPairs
public import Oberwolfach.MarkedWheelEventScales

@[expose] public section

/-! Pair loads for distinct actual rim/spoke resources of canonical
marked wheels. Auxiliary endpoint coincidences are checked explicitly. -/
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

theorem marked_wheel_distinct_rim_pair (hm : 3≤m)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,w W≤B/(Fintype.card V:ℝ)^m) (e f : E⊕K) (hef : e≠f) :
    (∑ W,if markedPhysicalEdge tail head ktail khead π e∈markedCyclePhysicalEdges tail head ktail khead m π b W.1 ∧
      markedPhysicalEdge tail head ktail khead π f∈markedCyclePhysicalEdges tail head ktail khead m π b W.1 then w W else 0)≤
      ((m:ℝ)+1)^4*B/Fintype.card V := by
  let P (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :=
    markedPhysicalEdge tail head ktail khead π e∈markedCyclePhysicalEdges tail head ktail khead m π b W.1 ∧
    markedPhysicalEdge tail head ktail khead π f∈markedCyclePhysicalEdges tail head ktail khead m π b W.1
  change (∑ W,if P W then w W else 0)≤_
  by_cases hex : ∃ W,P W
  · obtain ⟨W,hW⟩ := hex
    let S : Finset V := {Sum.elim tail ktail e,Sum.elim head khead e,Sum.elim tail ktail f,Sum.elim head khead f}
    have hS : 3≤S.card := marked_cycle_arc_pair_root_card (by omega) hp W.1 e f hef hW.1 hW.2
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
        have he := marked_cycle_arc_endpoints_present hp Z.1 e hZ.1
        have hf := marked_cycle_arc_endpoints_present hp Z.1 f hZ.2
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

theorem marked_wheel_rim_spoke_pair (hm : 1≤m)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hn : 0<Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,w W≤B/(Fintype.card V:ℝ)^m) (e : E⊕K) (v : V) (u : U) :
    (∑ W,if markedPhysicalEdge tail head ktail khead π e∈markedCyclePhysicalEdges tail head ktail khead m π b W.1 ∧
      (W.2.val=u ∧ v∈Set.range W.1.val) then w W else 0)≤
      ((m:ℝ)+1)^2*B/Fintype.card V := by
  let P (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :=
    markedPhysicalEdge tail head ktail khead π e∈markedCyclePhysicalEdges tail head ktail khead m π b W.1 ∧
      (W.2.val=u ∧ v∈Set.range W.1.val)
  change (∑ W,if P W then w W else 0)≤_
  by_cases hex : ∃ W,P W
  · obtain ⟨W,hW⟩ := hex
    have hne := marked_cycle_arc_nonloop hm hp W.1 e hW.1
    let S : Finset V := {Sum.elim tail ktail e,Sum.elim head khead e}
    have hS : S.card=2 := by simp [S,hne]
    have hbound := marked_wheel_fixed_hub_event hn w B hB hw S (by omega) (by omega) u P
      (by
        intro Z hZ
        refine ⟨?_,hZ.2.1⟩
        intro z hz
        have he := marked_cycle_arc_endpoints_present hp Z.1 e hZ.1
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

theorem marked_wheel_spoke_pair (hm : 1≤m) (hn : 0<Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,w W≤B/(Fintype.card V:ℝ)^m) (x y : V) (hxy : x≠y) (u : U) :
    (∑ W,if W.2.val=u ∧ x∈Set.range W.1.val ∧ y∈Set.range W.1.val then w W else 0)≤
      ((m:ℝ)+1)^2*B/Fintype.card V := by
  have hc : ({x,y}:Finset V).card=2 := by simp [hxy]
  have hh := marked_wheel_fixed_hub_event hn w B hB hw {x,y} (by rw [hc];omega)
    (by rw [hc];omega) u
    (fun W=>W.2.val=u ∧ x∈Set.range W.1.val ∧ y∈Set.range W.1.val)
    (by
      intro W h
      refine ⟨?_,h.1⟩
      intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl|rfl
      · exact h.2.1
      · exact h.2.2)
  simp only [hc,show 2-1=1 from rfl,pow_one] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro W _
  split_ifs <;> rfl

theorem marked_wheel_active_pair_load [Fintype E] [Fintype K] (hm : 3≤m)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,w W≤B/(Fintype.card V:ℝ)^m)
    (e f : MarkedActiveEdge E K H₀ Hₖ) (hef : e≠f) :
    (∑ W,if e∈markedActiveResources W ∧ f∈markedActiveResources W then w W else 0)≤
      ((m:ℝ)+1)^4*B/Fintype.card V := by
  have hscale : ((m:ℝ)+1)^2*B/Fintype.card V≤((m:ℝ)+1)^4*B/Fintype.card V := by
    simpa only [pow_one] using uniform_wheel_pair_scale _ _ B
      (by exact_mod_cast (show 1≤Fintype.card V by omega))
      (by linarith [show (0:ℝ)≤m from Nat.cast_nonneg m]) hB 2 1 (by omega) (by omega)
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      simp only [markedActiveResources_rim]
      exact marked_wheel_distinct_rim_pair hm hp hn hu w B hB hw e f
        (by intro he;exact hef (congrArg Sum.inl he))
    | inr f =>
      simp only [markedActiveResources_rim,markedActiveResources_spoke]
      exact (marked_wheel_rim_spoke_pair (by omega) hp hn w B hB hw e f.val.1 f.val.2).trans hscale
  | inr e =>
    cases f with
    | inl f =>
      simp only [markedActiveResources_rim,markedActiveResources_spoke]
      simpa only [and_comm] using
        (marked_wheel_rim_spoke_pair (by omega) hp hn w B hB hw f e.val.1 e.val.2).trans hscale
    | inr f =>
      simp only [markedActiveResources_spoke]
      by_cases huv : e.val.2=f.val.2
      · have hxy : e.val.1≠f.val.1 := by
          intro hxy
          exact hef (congrArg Sum.inr (Subtype.ext (Prod.ext hxy huv)))
        have hh := (marked_wheel_spoke_pair (by omega) hn w B hB hw e.val.1 f.val.1 hxy f.val.2).trans hscale
        simpa only [huv,and_assoc,and_left_comm,and_self_left] using hh
      · have hfalse (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :
            ¬((W.2.val=e.val.2 ∧ e.val.1∈Set.range W.1.val) ∧
              (W.2.val=f.val.2 ∧ f.val.1∈Set.range W.1.val)) :=
            fun h=>huv (h.1.1.symm.trans h.2.1)
        simp only [hfalse,ite_false,Finset.sum_const_zero]
        positivity

end Oberwolfach
