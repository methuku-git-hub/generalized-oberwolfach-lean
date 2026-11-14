module

public import Oberwolfach.TypedMarkedForbiddenSetCost

@[expose] public section

/-! Potential-load comparison after removing row and hub sets. The error
uses their cardinalities, and is proved only at roots outside those sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

theorem typedMarkedPotentialLoad_vertex_deletion (hm:2≤m)
    (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:MarkedWheel tail head ktail khead m π b H₀ HK→ℝ) (B:ℝ) (hB:0≤B)
    (hw0:∀ W,0≤w W) (hw:∀ W,w W≤B/(Fintype.card V:ℝ)^m)
    (R:E⊕K→Prop) (H:Bool→V→U→Prop) (T:Finset V) (Z:Finset U)
    (e:(E⊕K)⊕(Bool×V×U))
    (he:Sum.elim (fun a=>Sum.elim tail ktail a∉T∧Sum.elim head khead a∉T)
      (fun s=>s.2.1∉T∧s.2.2∉Z) e):
    |typedMarkedPotentialLoad w
      (fun a=>R a∧Sum.elim tail ktail a∉T∧Sum.elim head khead a∉T)
      (fun j v u=>H j v u∧v∉T∧u∉Z) e-typedMarkedPotentialLoad w R H e|
      ≤((T.card:ℝ)+Z.card)*((m:ℝ)+1)^3*B/Fintype.card V:=by
  let Good:=fun W:MarkedWheel tail head ktail khead m π b H₀ HK=>
    (∀ x∈T,x∉Set.range W.1.val)∧W.2.val∉Z
  have hc:=resourceRootOmittedLoad_exceptional_candidates typedMarkedOccurrenceResources w hw0
    (Sum.elim R (fun s=>H s.1 s.2.1 s.2.2))
    (Sum.elim (fun a=>R a∧Sum.elim tail ktail a∉T∧Sum.elim head khead a∉T)
      (fun s=>H s.1 s.2.1 s.2.2∧s.2.1∉T∧s.2.2∉Z)) Good
    (by
      intro W hW a ha
      cases a with
      | inl a=>
        have hend:=canonicalMarkedArc_endpoints_present W.1 a ((typedMarkedOccurrenceResources_rim W a).mp ha)
        have ht:Sum.elim tail ktail a∉T:=fun h=>hW.1 _ h hend.1
        have hh:Sum.elim head khead a∉T:=fun h=>hW.1 _ h hend.2
        exact ⟨fun h=>⟨h,ht,hh⟩,fun h=>h.1⟩
      | inr s=>
        obtain ⟨i,hi⟩:=(typedMarkedOccurrenceResources_spoke W s).mp ha
        have hv:W.1.val i=s.2.1:=congrArg (fun s:Bool×V×U=>s.2.1) hi
        have hu':W.2.val=s.2.2:=congrArg (fun s:Bool×V×U=>s.2.2) hi
        have ht:s.2.1∉T:=fun h=>hW.1 _ h ⟨i,hv⟩
        have hh:s.2.2∉Z:=by simpa only [hu'] using hW.2
        exact ⟨fun h=>⟨h,ht,hh⟩,fun h=>h.1⟩) e
  have hbad (W:MarkedWheel tail head ktail khead m π b H₀ HK):
      ¬Good W↔(∃ x∈T,x∈Set.range W.1.val)∨W.2.val∈Z:=by
    by_cases hr:∃ x∈T,x∈Set.range W.1.val
    · constructor
      · intro _;exact Or.inl hr
      · intro _ hg
        obtain ⟨x,hx,hC⟩:=hr
        exact hg.1 x hx hC
    · have hh:∀ x∈T,x∉Set.range W.1.val:=fun x hx hc=>hr ⟨x,hx,hc⟩
      constructor
      · intro h
        right
        by_contra hz
        exact h ⟨hh,hz⟩
      · intro h hg
        rcases h with hr'|hz
        · exact hr hr'
        · exact hg.2 hz
  have hsum:(∑ W,if e∈typedMarkedOccurrenceResources W∧¬Good W then w W else 0)=
      ∑ W,if e∈typedMarkedOccurrenceResources W∧((∃ x∈T,x∈Set.range W.1.val)∨W.2.val∈Z) then w W else 0:=by
    apply Finset.sum_congr rfl
    intro W _
    by_cases h:e∈typedMarkedOccurrenceResources W∧¬Good W
    · rw [if_pos h,if_pos ⟨h.1,(hbad W).mp h.2⟩]
    · rw [if_neg h,if_neg (fun hh=>h ⟨hh.1,(hbad W).mpr hh.2⟩)]
  have hc': |typedMarkedPotentialLoad w
      (fun a=>R a∧Sum.elim tail ktail a∉T∧Sum.elim head khead a∉T)
      (fun j v u=>H j v u∧v∉T∧u∉Z) e-typedMarkedPotentialLoad w R H e|≤
      ∑ W,if e∈typedMarkedOccurrenceResources W∧¬Good W then w W else 0:=by
    convert hc using 1 <;> congr!
  rw [hsum] at hc'
  exact hc'.trans (typedMarked_forbidden_set_weight hm hn hu w B hB hw0 hw T Z e he)

end Oberwolfach
