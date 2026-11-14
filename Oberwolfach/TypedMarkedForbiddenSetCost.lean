module

public import Oberwolfach.TypedMarkedVertexExclusionWeights
public import Oberwolfach.ResourceCandidateExceptionalCost

@[expose] public section

/-! Removing fixed row and hub sets has a cost proportional to their
cardinalities at every root outside those sets. All candidates and weights
are still those of the original potential universe. -/
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

theorem typedMarked_forbidden_set_weight (hm:2≤m)
    (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:MarkedWheel tail head ktail khead m π b H₀ HK→ℝ) (B:ℝ) (hB:0≤B)
    (hw0:∀ W,0≤w W) (hw:∀ W,w W≤B/(Fintype.card V:ℝ)^m)
    (T:Finset V) (Z:Finset U) (e:(E⊕K)⊕(Bool×V×U))
    (he:Sum.elim (fun a=>Sum.elim tail ktail a∉T∧Sum.elim head khead a∉T)
      (fun s=>s.2.1∉T∧s.2.2∉Z) e):
    (∑ W,if e∈typedMarkedOccurrenceResources W∧
      ((∃ x∈T,x∈Set.range W.1.val)∨W.2.val∈Z) then w W else 0)
      ≤((T.card:ℝ)+Z.card)*((m:ℝ)+1)^3*B/Fintype.card V:=by
  let Q:=fun z:V⊕U=>fun W:MarkedWheel tail head ktail khead m π b H₀ HK=>
    Sum.elim (fun x=>x∈Set.range W.1.val) (fun u=>W.2.val=u) z
  have hbad (W:MarkedWheel tail head ktail khead m π b H₀ HK):
      (∃ z∈T.disjSum Z,Q z W)↔(∃ x∈T,x∈Set.range W.1.val)∨W.2.val∈Z:=by
    constructor
    · rintro ⟨z,hz,hQ⟩
      cases z with
      | inl x=>exact Or.inl ⟨x,by simpa only [Finset.inl_mem_disjSum] using hz,hQ⟩
      | inr u=>exact Or.inr (hQ ▸ (by simpa only [Finset.inr_mem_disjSum] using hz))
    · rintro (⟨x,hx,hC⟩|hU)
      · exact ⟨Sum.inl x,by simpa using hx,hC⟩
      · exact ⟨Sum.inr W.2.val,by simpa using hU,rfl⟩
  have hunion:=finite_weighted_exception_union (T.disjSum Z) w hw0
    (fun W=>e∈typedMarkedOccurrenceResources W) Q
  have heq:(∑ W,if e∈typedMarkedOccurrenceResources W∧
      ((∃ x∈T,x∈Set.range W.1.val)∨W.2.val∈Z) then w W else 0)=
      ∑ W,if e∈typedMarkedOccurrenceResources W∧(∃ z∈T.disjSum Z,Q z W) then w W else 0:=by
    apply Finset.sum_congr rfl
    intro W _
    by_cases h:e∈typedMarkedOccurrenceResources W∧((∃ x∈T,x∈Set.range W.1.val)∨W.2.val∈Z)
    · rw [if_pos h,if_pos ⟨h.1,(hbad W).mpr h.2⟩]
    · rw [if_neg h,if_neg (fun hh=>h ⟨hh.1,(hbad W).mp hh.2⟩)]
  rw [heq]
  have hunion' : (∑ W,if e∈typedMarkedOccurrenceResources W∧(∃ z∈T.disjSum Z,Q z W) then w W else 0)≤
      ∑ z∈T.disjSum Z,∑ W,if e∈typedMarkedOccurrenceResources W∧Q z W then w W else 0:=by
    convert hunion using 1 <;> congr!
  apply hunion'.trans
  have h23:((m:ℝ)+1)^2*B/Fintype.card V≤((m:ℝ)+1)^3*B/Fintype.card V:=by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_right _ hB
    exact pow_le_pow_right₀ (show (1:ℝ)≤(m:ℝ)+1 by linarith [show (0:ℝ)≤m from Nat.cast_nonneg m]) (by omega)
  have hterm:∀ z∈T.disjSum Z,(∑ W,if e∈typedMarkedOccurrenceResources W∧Q z W then w W else 0)
      ≤((m:ℝ)+1)^3*B/Fintype.card V:=by
    intro z hz
    cases e with
    | inl a=>
      cases z with
      | inl x=>
        have hx:x∈T:=by simpa only [Finset.inl_mem_disjSum] using hz
        have hnot:x∉({Sum.elim tail ktail a,Sum.elim head khead a}:Finset V):=by
          simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
          exact ⟨fun h=>he.1 (h ▸ hx),fun h=>he.2 (h ▸ hx)⟩
        simpa only [typedMarkedOccurrenceResources_rim,Q,Sum.elim_inl] using
          canonical_marked_rim_extra_row_weight hm hn hu w B hB hw a x hnot
      | inr u=>
        simpa only [typedMarkedOccurrenceResources_rim,Q,Sum.elim_inr] using
          (canonical_marked_rim_fixed_hub_weight (by omega) hn w B hB hw a u).trans h23
    | inr s=>
      cases z with
      | inl x=>
        have hx:x∈T:=by simpa only [Finset.inl_mem_disjSum] using hz
        have hne:x≠s.2.1:=fun h=>he.1 (h ▸ hx)
        convert (typedMarked_spoke_extra_row_weight (by omega) hn w B hB hw0 hw s.1 s.2.1 x hne s.2.2).trans h23 using 1 <;> congr!
      | inr u=>
        have hz:u∈Z:=by simpa only [Finset.inr_mem_disjSum] using hz
        have hne:u≠s.2.2:=fun h=>he.2 (h ▸ hz)
        have hz0 : (∑ W,if Sum.inr s∈typedMarkedOccurrenceResources W∧Q (Sum.inr u) W then w W else 0)=0:=by
          convert typedMarked_spoke_other_hub_weight_zero w s.1 s.2.1 s.2.2 u hne using 1 <;> congr!
        rw [hz0]
        positivity
  have hsum:=Finset.sum_le_sum hterm
  simpa only [Finset.sum_const,nsmul_eq_mul,Finset.card_disjSum,Nat.cast_add,mul_div_assoc,mul_assoc] using hsum

end Oberwolfach
