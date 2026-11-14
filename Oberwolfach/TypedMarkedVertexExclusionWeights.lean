module

public import Oberwolfach.TypedMarkedPotentialResources
public import Oberwolfach.CanonicalMarkedPairBounds

@[expose] public section

/-! Fixed-weight cost of a forbidden row or hub at a retained typed root.
Only genuinely free vertices are counted; a root's own row is excluded. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

theorem canonical_marked_rim_extra_row_weight (hm:2≤m)
    (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:MarkedWheel tail head ktail khead m π b H₀ HK→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀ W,w W≤B/(Fintype.card V:ℝ)^m) (e:E⊕K) (x:V)
    (hx:x∉({Sum.elim tail ktail e,Sum.elim head khead e}:Finset V)):
    (∑ W,if CanonicalMarkedArcMem W.1 e∧x∈Set.range W.1.val then w W else 0)
      ≤((m:ℝ)+1)^3*B/Fintype.card V:=by
  let P:=fun W:MarkedWheel tail head ktail khead m π b H₀ HK=>CanonicalMarkedArcMem W.1 e∧x∈Set.range W.1.val
  by_cases hex:∃ W,P W
  · obtain ⟨W,hW⟩:=hex
    have hne:=canonicalMarkedArc_nonloop (by omega) W.1 e hW.1
    let S:Finset V:=insert x {Sum.elim tail ktail e,Sum.elim head khead e}
    have hS:S.card=3:=by dsimp [S];rw [Finset.card_insert_of_notMem hx];simp [hne]
    have hh:=marked_wheel_free_hub_event hn hu w B hB hw S (by omega) (by omega) P
      (by
        intro W hW y hy
        have he:=canonicalMarkedArc_endpoints_present W.1 e hW.1
        simp only [S,Finset.mem_insert,Finset.mem_singleton] at hy
        rcases hy with rfl|rfl|rfl
        · exact hW.2
        · exact he.1
        · exact he.2)
    simp only [hS,show 3-2=1 from rfl,pow_one] at hh
    convert hh using 1 <;> congr!
  · have hfalse:∀ W,¬P W:=by simpa only [not_exists] using hex
    change (∑ W,if P W then w W else 0)≤_
    simp only [hfalse,ite_false,Finset.sum_const_zero]
    positivity

theorem canonical_marked_rim_fixed_hub_weight (hm:1≤m)
    (hn:0<Fintype.card V)
    (w:MarkedWheel tail head ktail khead m π b H₀ HK→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀ W,w W≤B/(Fintype.card V:ℝ)^m) (e:E⊕K) (u:U):
    (∑ W,if CanonicalMarkedArcMem W.1 e∧W.2.val=u then w W else 0)
      ≤((m:ℝ)+1)^2*B/Fintype.card V:=by
  let P:=fun W:MarkedWheel tail head ktail khead m π b H₀ HK=>CanonicalMarkedArcMem W.1 e∧W.2.val=u
  by_cases hex:∃ W,P W
  · obtain ⟨W,hW⟩:=hex
    have hne:=canonicalMarkedArc_nonloop hm W.1 e hW.1
    let S:Finset V:={Sum.elim tail ktail e,Sum.elim head khead e}
    have hS:S.card=2:=by simp [S,hne]
    have hh:=marked_wheel_fixed_hub_event hn w B hB hw S (by omega) (by omega) u P
      (by
        intro W hW
        refine ⟨?_,hW.2⟩
        intro y hy
        have he:=canonicalMarkedArc_endpoints_present W.1 e hW.1
        simp only [S,Finset.mem_insert,Finset.mem_singleton] at hy
        rcases hy with rfl|rfl
        · exact he.1
        · exact he.2)
    simp only [hS,show 2-1=1 from rfl,pow_one] at hh
    convert hh using 1 <;> congr!
  · have hfalse:∀ W,¬P W:=by simpa only [not_exists] using hex
    change (∑ W,if P W then w W else 0)≤_
    simp only [hfalse,ite_false,Finset.sum_const_zero]
    positivity

theorem typedMarked_spoke_extra_row_weight (hm:1≤m) (hn:0<Fintype.card V)
    (w:MarkedWheel tail head ktail khead m π b H₀ HK→ℝ) (B:ℝ) (hB:0≤B)
    (hw0:∀ W,0≤w W) (hw:∀ W,w W≤B/(Fintype.card V:ℝ)^m)
    (j:Bool) (v x:V) (hx:x≠v) (u:U):
    (∑ W,if Sum.inr (j,v,u)∈typedMarkedOccurrenceResources W∧x∈Set.range W.1.val then w W else 0)
      ≤((m:ℝ)+1)^2*B/Fintype.card V:=by
  apply le_trans _ (marked_wheel_spoke_pair hm hn w B hB hw v x (Ne.symm hx) u)
  apply Finset.sum_le_sum
  intro W _
  by_cases h:Sum.inr (j,v,u)∈typedMarkedOccurrenceResources W∧x∈Set.range W.1.val
  · obtain ⟨i,hi⟩:=(typedMarkedOccurrenceResources_spoke W (j,v,u)).mp h.1
    have hv:W.1.val i=v:=congrArg (fun z:Bool×V×U=>z.2.1) hi
    have hu:W.2.val=u:=congrArg (fun z:Bool×V×U=>z.2.2) hi
    rw [if_pos h,if_pos ⟨hu,⟨i,hv⟩,h.2⟩]
  · rw [if_neg h]
    split_ifs <;> first | exact hw0 W | rfl

theorem typedMarked_spoke_other_hub_weight_zero
    (w:MarkedWheel tail head ktail khead m π b H₀ HK→ℝ)
    (j:Bool) (v:V) (u z:U) (hz:z≠u):
    (∑ W,if Sum.inr (j,v,u)∈typedMarkedOccurrenceResources W∧W.2.val=z then w W else 0)=0:=by
  apply Finset.sum_eq_zero
  intro W _
  apply if_neg
  rintro ⟨hm,he⟩
  obtain ⟨i,hi⟩:=(typedMarkedOccurrenceResources_spoke W (j,v,u)).mp hm
  exact hz (he.symm.trans (congrArg (fun s:Bool×V×U=>s.2.2) hi))

end Oberwolfach
