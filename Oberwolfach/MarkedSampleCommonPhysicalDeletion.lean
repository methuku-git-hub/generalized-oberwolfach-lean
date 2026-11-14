module

public import Oberwolfach.MarkedPhysicalCutTransfer
public import Oberwolfach.CommonMarkedPathConstraintCounts

@[expose] public section

/-! Common cycle and root-omitted path counts in the actual sample after
physical deletion. These compare the original and remaining sample on the
same vertex domain, with no resampling or change of type. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_rim_relation_deletion_bounds
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (DR:SimpleGraph V) (δ:ℝ) (hDR:∀ x,(DR.degree x:ℝ)≤δ):
    let R:=fun mark x y=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1
    let R':=fun mark x y=>markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark x y=1;
    (∀ mark x,(∑ y,bipAdj (fun x y=>R mark x y∧¬R' mark x y) x y)≤δ)∧
    (∀ mark y,(∑ x,bipAdj (fun x y=>R mark x y∧¬R' mark x y) x y)≤δ):=by
  intro R R'
  have hchange (a:Bool×Bool×V):
      (∑ z,if rawMarkedPairRims P π d σ (markedRowRim a z)∧
        ¬rawMarkedPairRims P π d (rawMarkedDeleteRims σ DR.edgeFinset) (markedRowRim a z)
          then (1:ℝ) else 0)≤δ:=by
    apply le_trans _ ((marked_row_rim_physical_deletion_change P π d σ DR Finset.univ a).trans (hDR _))
    apply Finset.sum_le_sum
    intro z _
    by_cases h:rawMarkedPairRims P π d σ (markedRowRim a z) <;>
      by_cases h':rawMarkedPairRims P π d (rawMarkedDeleteRims σ DR.edgeFinset) (markedRowRim a z) <;>
        simp [h,h']
  constructor
  · intro mark x
    have hh:=hchange (mark,false,x)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro y _
    cases mark <;> simp only [R,R',bipAdj,rawMarkedPairRims,markedRowRim,
      Bool.false_eq_true,ite_false,ite_true,Sum.elim_inl,Sum.elim_inr] <;> split_ifs <;> rfl
  · intro mark y
    have hh:=hchange (mark,true,y)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro x _
    cases mark <;> simp only [R,R',bipAdj,rawMarkedPairRims,markedRowRim,
      Bool.false_eq_true,ite_false,ite_true,Sum.elim_inl,Sum.elim_inr] <;> split_ifs <;> rfl

theorem marked_spoke_relation_deletion_bound (H:Bool→V→U→Prop) (DS:SimpleGraph (V⊕U))
    (δ:ℝ) (hDS:∀ u,(DS.degree (Sum.inr u):ℝ)≤δ):
    ∀ mark u,(∑ x,if H mark x u∧¬markedDeletePhysicalSpokes H DS mark x u then (1:ℝ) else 0)≤δ:=by
  intro mark u
  apply le_trans _ ((marked_spoke_physical_deletion_column_change H DS Finset.univ mark u).trans (hDS u))
  apply Finset.sum_le_sum
  intro x _
  by_cases h:H mark x u <;> by_cases h':markedDeletePhysicalSpokes H DS mark x u <;> simp [h,h']

theorem marked_sample_common_cycle_physical_deletion
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:1≤m)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)) (δ:ℝ)
    (hDR:∀ x,(DR.degree x:ℝ)≤δ) (hDS:∀ u,(DS.degree (Sum.inr u):ℝ)≤δ) (u u':U):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    (Fintype.card (CommonMarkedCycle (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true) u u'):ℝ)-
    Fintype.card (CommonMarkedCycle (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) m π (3*d)
      (markedDeletePhysicalSpokes H DS false) (markedDeletePhysicalSpokes H DS true) u u')≤
      3*((m:ℝ)+1)*δ*(Fintype.card V:ℝ)^m:=by
  intro E K σ' E' K'
  let R:=fun mark x y=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1
  let R':=fun mark x y=>markedPhysicalRim P π (3*d) (fun e=>σ' (Sum.inl e)) mark x y=1
  have hR:=marked_rim_relation_deletion_bounds P π d σ DR δ hDR
  have hH:=marked_spoke_relation_deletion_bound H DS δ hDS
  have hh:=commonMarkedCycle_constraint_loss hm R R' H (markedDeletePhysicalSpokes H DS)
    (PermutationSeparated π (3*d)) u u' δ hR.1 hH
  rw [Fintype.card_congr (commonMarkedCycleConstraintsEquiv (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π (3*d) (H false) (H true) u u'),
    Fintype.card_congr (commonMarkedCycleConstraintsEquiv (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) π (3*d)
      (markedDeletePhysicalSpokes H DS false) (markedDeletePhysicalSpokes H DS true) u u')]
  have he (τ:RawMarkedOutcome V U Γ Color):
      (fun mark x y=>if mark then ∃ e:MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true,e.val.1=x∧e.val.2=y
        else ∃ e:MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false,e.val.1=x∧e.val.2=y)=
      fun mark x y=>markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1:=by
    funext mark x y;apply propext;cases mark <;> simp only [Bool.false_eq_true,ite_false,ite_true,markedSampleArc_indicator_iff]
  have heH (HH:Bool→V→U→Prop):(fun mark=>if mark then HH true else HH false)=HH:=by
    funext mark;cases mark <;> rfl
  dsimp only [E,K,E',K']
  rw [he σ,he σ']
  simp only [heH]
  exact hh

theorem marked_sample_common_path_physical_deletion
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:1≤m)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)) (δ:ℝ)
    (hDR:∀ x,(DR.degree x:ℝ)≤δ) (hDS:∀ u,(DS.degree (Sum.inr u):ℝ)≤δ)
    (i:Fin (m+1)) (v v':V) (u u':U):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    (Fintype.card (CanonicalCommonMarkedPath (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true) i v v' u u'):ℝ)-
    Fintype.card (CanonicalCommonMarkedPath (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) m π (3*d)
      (markedDeletePhysicalSpokes H DS false) (markedDeletePhysicalSpokes H DS true) i v v' u u')≤
      4*((m:ℝ)+1)*δ*(Fintype.card V:ℝ)^(m-1):=by
  intro E K σ' E' K'
  let R:=fun mark x y=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1
  let R':=fun mark x y=>markedPhysicalRim P π (3*d) (fun e=>σ' (Sum.inl e)) mark x y=1
  have hR:=marked_rim_relation_deletion_bounds P π d σ DR δ hDR
  have hH:=marked_spoke_relation_deletion_bound H DS δ hDS
  have hh:=commonMarkedPath_constraint_loss hm R R' H (markedDeletePhysicalSpokes H DS)
    (fun z=>PermutationSeparated π (3*d) (Fin.insertNth i v z)∧PermutationSeparated π (3*d) (Fin.insertNth i v' z))
    i v v' u u' δ hR.1 hR.2 hH
  rw [Fintype.card_congr (commonMarkedPathConstraintsEquiv (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π (3*d) (H false) (H true) i v v' u u'),
    Fintype.card_congr (commonMarkedPathConstraintsEquiv (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) π (3*d)
      (markedDeletePhysicalSpokes H DS false) (markedDeletePhysicalSpokes H DS true) i v v' u u')]
  have he (τ:RawMarkedOutcome V U Γ Color):
      (fun mark x y=>if mark then ∃ e:MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true,e.val.1=x∧e.val.2=y
        else ∃ e:MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false,e.val.1=x∧e.val.2=y)=
      fun mark x y=>markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1:=by
    funext mark x y;apply propext;cases mark <;> simp only [Bool.false_eq_true,ite_false,ite_true,markedSampleArc_indicator_iff]
  have heH (HH:Bool→V→U→Prop):(fun mark=>if mark then HH true else HH false)=HH:=by
    funext mark;cases mark <;> rfl
  dsimp only [E,K,E',K']
  rw [he σ,he σ']
  simp only [heH]
  simp only [Fintype.card_eq_nat_card] at hh ⊢
  exact hh

end Oberwolfach
