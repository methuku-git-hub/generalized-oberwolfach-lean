module

public import Oberwolfach.MarkedModifiedPhysicalIncidence
public import Oberwolfach.MarkedReferenceAfterPhysicalDeletion

@[expose] public section
/-! Reference rim degrees and two-step counts after additions, deletions,
reorientations or retypings, with unchanged interval coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_rim_degree_physical_change
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ τ:RawMarkedOutcome V U Γ Color)
    (DR:SimpleGraph V) (mark:Bool) (x:V)
    (hchange:∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→
      markedPairPhysical π a∈DR.edgeFinset):
    let M:=markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark
    let M':=markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark;
    |(∑ y,(M' x y:ℝ))-(∑ y,(M x y:ℝ))|≤DR.degree x ∧
    |(∑ y,(M' y x:ℝ))-(∑ y,(M y x:ℝ))|≤DR.degree (if mark then π x else x):=by
  intro M M'
  have hr (incoming:Bool):
      |(∑ y,if rawMarkedPairRims P π d τ (markedRowRim (mark,incoming,x) y) then (1:ℝ) else 0)-
        (∑ y,if rawMarkedPairRims P π d σ (markedRowRim (mark,incoming,x) y) then (1:ℝ) else 0)|≤
        DR.degree (if mark && incoming then π x else x):=
    (finset_indicator_sum_change Finset.univ _ _).trans
      (marked_row_rim_physical_change P π d σ τ DR hchange mark incoming x)
  have he (θ:RawMarkedOutcome V U Γ Color) (a b:V):
      (if markedPhysicalRim P π (3*d) (fun e=>θ (Sum.inl e)) mark a b=1 then (1:ℝ) else 0)=
        (markedPhysicalRim P π (3*d) (fun e=>θ (Sum.inl e)) mark a b:ℝ):=by
    exact_mod_cast markedPhysicalRim_indicator P π (3*d) (fun e=>θ (Sum.inl e)) mark a b
  constructor
  · cases mark <;> simpa [M,M',markedRowRim,rawMarkedPairRims,he] using hr false
  · cases mark <;> simpa [M,M',markedRowRim,rawMarkedPairRims,he] using hr true

theorem marked_rim_two_step_physical_change
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ τ:RawMarkedOutcome V U Γ Color)
    (DR:SimpleGraph V) (mark:Bool) (δ:ℝ) (hDR:∀ x,(DR.degree x:ℝ)≤δ)
    (hchange:∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→
      markedPairPhysical π a∈DR.edgeFinset) (x y:V):
    let R:=fun a b=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark a b=1
    let Q:=fun a b=>markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark a b=1;
    |((Finset.univ.filter (fun z=>Q x z∧Q z y)).card:ℝ)-
      (Finset.univ.filter (fun z=>R x z∧R z y)).card|≤2*δ:=by
  intro R Q
  have hout:(∑ z,if ¬(R x z↔Q x z) then (1:ℝ) else 0)≤δ:=by
    have hh:=(marked_row_rim_physical_change P π d σ τ DR hchange mark false x).trans (hDR _)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro z _
    cases mark <;> simp only [R,Q,rawMarkedPairRims,markedRowRim,Bool.false_eq_true,ite_false,ite_true,Sum.elim_inl,Sum.elim_inr]
  have hin:(∑ z,if ¬(R z y↔Q z y) then (1:ℝ) else 0)≤δ:=by
    have hh:=(marked_row_rim_physical_change P π d σ τ DR hchange mark true y).trans (hDR _)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro z _
    cases mark <;> simp only [R,Q,rawMarkedPairRims,markedRowRim,Bool.false_eq_true,ite_false,ite_true,Sum.elim_inl,Sum.elim_inr]
  have hh:=relation_two_step_changes R Q x y δ δ (by convert hout using 1 <;> congr!) (by convert hin using 1 <;> congr!)
  rw [←two_mul] at hh
  convert hh using 1 <;> congr!

theorem marked_reference_statistics_after_physical_change
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (g:Γ) (j:Color)
    (D ε δ γ γ' p k s t ζ:ℝ) (σ τ:RawMarkedOutcome V U Γ Color) (DR:SimpleGraph V)
    (hinterval:∀ e,σ (Sum.inr e)=τ (Sum.inr e))
    (hchange:∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→
      markedPairPhysical π a∈DR.edgeFinset)
    (hDR:∀ x,(DR.degree x:ℝ)≤ζ*Fintype.card V)
    (hmargin:2*ζ≤(3/2)*(γ-γ')*p^2)
    (hstats:MarkedReferenceStatistics P π d g j D ε δ γ p k s t σ):
    MarkedReferenceStatistics P π d g j D (ε+ζ) δ γ' p k s t τ :=by
  have hinter:(fun e=>σ (Sum.inr e))=(fun e=>τ (Sum.inr e)):=funext hinterval
  have hsp:rawMarkedPairSpokes π d σ g j=rawMarkedPairSpokes π d τ g j:=by
    unfold rawMarkedPairSpokes
    rw [hinter]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro mark x
    have h:=marked_rim_degree_physical_change P π d σ τ DR mark x hchange
    have hc:=hstats.1.1 mark x
    simp only [←Nat.cast_sum] at h
    have hout:=(abs_sub_le
      (((∑ y,markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y):ℕ):ℝ)
      (((∑ y,markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y):ℕ):ℝ)
      ((if mark then k else p)*D)).trans (add_le_add (h.1.trans (hDR x)) hc.1)
    have hin:=(abs_sub_le
      (((∑ y,markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark y x):ℕ):ℝ)
      (((∑ y,markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark y x):ℕ):ℝ)
      ((if mark then k else p)*D)).trans (add_le_add (h.2.trans (hDR _)) hc.2)
    constructor <;> nlinarith only [hout,hin]
  · intro x y hxy
    have h:=marked_rim_two_step_physical_change P π d σ τ DR false (ζ*Fintype.card V) hDR hchange x y
    have hlo:=hstats.1.2 x y hxy
    simp only [markedPhysicalRim_pos_iff_one] at hlo ⊢
    have hloss:=(abs_le.mp h).1
    have hm:=mul_le_mul_of_nonneg_right hmargin (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
    nlinarith only [hlo,hloss,hm]
  · simpa only [←hsp] using hstats.2

theorem marked_rim_cut_physical_change_bound
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color) (DR:SimpleGraph V)
    (hchange:∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→
      markedPairPhysical π a∈DR.edgeFinset)
    (ζ:ℝ) (hζ:0≤ζ) (hDR:∀ x,(DR.degree x:ℝ)≤ζ*Fintype.card V)
    (mark:Bool) (S T:Finset V) :
    |(matrixCut (markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark) S T:ℝ)-
      (matrixCut (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark) S T:ℝ)|≤
      ζ*Fintype.card V*min (S.card:ℝ) T.card :=by
  let R:=fun x y=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1
  let R':=fun x y=>markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1
  have hr (x:V):(∑ y,if ¬(R x y↔R' x y) then (1:ℝ) else 0)≤ζ*Fintype.card V:=by
    have h:=(marked_row_rim_physical_change P π d σ τ DR hchange mark false x).trans (hDR _)
    cases mark <;> simpa [R,R',markedRowRim,rawMarkedPairRims] using h
  have hc (y:V):(∑ x,if ¬(R x y↔R' x y) then (1:ℝ) else 0)≤ζ*Fintype.card V:=by
    have h:=(marked_row_rim_physical_change P π d σ τ DR hchange mark true y).trans (hDR _)
    cases mark <;> simpa [R,R',markedRowRim,rawMarkedPairRims] using h
  have h:=bipartite_cut_change_degrees R R' ζ hζ
    (by intro x;convert hr x using 1 <;> congr!) (by intro x;convert hc x using 1 <;> congr!) S T
  have hi (θ:RawMarkedOutcome V U Γ Color):
      (fun x y=>@ite ℕ (markedPhysicalRim P π (3*d) (fun e=>θ (Sum.inl e)) mark x y=1)
        (Classical.propDecidable _) 1 0)=markedPhysicalRim P π (3*d) (fun e=>θ (Sum.inl e)) mark:=by
    funext x y
    split_ifs with hh
    · exact hh.symm
    · have hh':=markedPhysicalRim_indicator P π (3*d) (fun e=>θ (Sum.inl e)) mark x y
      simpa only [hh,ite_false] using hh'
  dsimp only [R,R'] at h
  rw [hi,hi] at h
  change |(matrixCut _ S T:ℝ)-(matrixCut _ S T:ℝ)|≤_ at h
  rw [←mul_min_of_nonneg _ _ (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))] at h
  simpa only [mul_assoc] using h

theorem marked_reference_cuts_after_physical_change
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (g:Γ) (j:Color)
    (α α' p k t ζ:ℝ) (ha:α'≤α) (hζ:0≤ζ)
    (hmargin:∀ mark:Bool,ζ≤(α-α')*(if mark then k else p)/4)
    (σ τ:RawMarkedOutcome V U Γ Color) (DR:SimpleGraph V)
    (hinterval:∀ e,σ (Sum.inr e)=τ (Sum.inr e))
    (hchange:∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→
      markedPairPhysical π a∈DR.edgeFinset)
    (hDR:∀ x,(DR.degree x:ℝ)≤ζ*Fintype.card V)
    (hcuts:MarkedReferenceCutFamilies P π d g j α p k t σ):
    MarkedReferenceCutFamilies P π d g j α' p k t τ :=by
  have hinter:(fun e=>σ (Sum.inr e))=(fun e=>τ (Sum.inr e)):=funext hinterval
  have hsp:rawMarkedPairSpokes π d σ g j=rawMarkedPairSpokes π d τ g j:=by
    unfold rawMarkedPairSpokes
    rw [hinter]
  refine ⟨?_,?_⟩
  · simpa only [←hsp] using hcuts.1
  · intro mark δ hdα hdp S T hST
    have hcut:=hcuts.2 mark δ (hdα.trans (by linarith only [ha])) hdp S T hST
    have hloss:=(abs_le.mp (marked_rim_cut_physical_change_bound P π d σ τ DR hchange ζ hζ hDR mark S T)).1
    have hm:=mul_le_mul_of_nonneg_right (hmargin mark)
      (show 0≤(Fintype.card V:ℝ)*min (S.card:ℝ) T.card by positivity)
    nlinarith only [hcut,hloss,hm]
end Oberwolfach
