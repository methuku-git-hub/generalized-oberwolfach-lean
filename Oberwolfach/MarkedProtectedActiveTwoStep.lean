module

public import Oberwolfach.MarkedPhysicalCutTransfer
public import Oberwolfach.FiniteTwoStepRestriction

@[expose] public section

/-! Two-step neighbourhoods of the actual active ordinary rim retain a
lower bound for every pair of distinct roots, including close roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_rim_two_step_physical_deletion
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (DR:SimpleGraph V) (mark:Bool) (δ:ℝ) (hDR:∀ x,(DR.degree x:ℝ)≤δ) (x y:V):
    let R:=fun a b=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark a b=1
    let Q:=fun a b=>markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark a b=1;
    |((Finset.univ.filter (fun z=>Q x z∧Q z y)).card:ℝ)-
      (Finset.univ.filter (fun z=>R x z∧R z y)).card|≤2*δ:=by
  intro R Q
  have hout:(∑ z,if ¬(R x z↔Q x z) then (1:ℝ) else 0)≤δ:=by
    have hh:=(marked_row_rim_physical_deletion_change P π d σ DR Finset.univ (mark,false,x)).trans (hDR _)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro z _
    cases mark <;> simp only [R,Q,rawMarkedPairRims,markedRowRim,Bool.false_eq_true,ite_false,ite_true,Sum.elim_inl,Sum.elim_inr]
  have hin:(∑ z,if ¬(R z y↔Q z y) then (1:ℝ) else 0)≤δ:=by
    have hh:=(marked_row_rim_physical_deletion_change P π d σ DR Finset.univ (mark,true,y)).trans (hDR _)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro z _
    cases mark <;> simp only [R,Q,rawMarkedPairRims,markedRowRim,Bool.false_eq_true,ite_false,ite_true,Sum.elim_inl,Sum.elim_inr]
  have hh:=relation_two_step_changes R Q x y δ δ (by convert hout using 1 <;> congr!) (by convert hin using 1 <;> congr!)
  rw [←two_mul] at hh
  convert hh using 1 <;> congr!

theorem marked_protected_active_two_step
    (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (DR:SimpleGraph V) (mark:Bool) (δ lower:ℝ)
    (hDR:∀ x,((DR.comap f).degree x:ℝ)≤δ)
    (hlower:∀ x y,x≠y→lower≤((Finset.univ.filter (fun z=>
      markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x z=1∧
      markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark z y=1)).card:ℝ)):
    let σA:=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset);
    ∀ x y:W,x≠y→lower-(Finset.univ\Finset.univ.image f).card-2*δ≤
      ((Finset.univ.filter (fun z=>
        (∃ e:MarkedSampleArc (P.comap f) ρ (3*d) (fun a=>σA (Sum.inl a)) mark,e.val.1=x∧e.val.2=z)∧
        (∃ e:MarkedSampleArc (P.comap f) ρ (3*d) (fun a=>σA (Sum.inl a)) mark,e.val.1=z∧e.val.2=y))).card:ℝ):=by
  intro σA x y hxy
  let σ₀:=rawMarkedRestrictPair f g σ
  let R:=fun a b=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark a b=1
  let R₀:=fun a b=>markedPhysicalRim (P.comap f) ρ (3*d) (fun e=>σ₀ (Sum.inl e)) mark a b=1
  let RA:=fun a b=>markedPhysicalRim (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) mark a b=1
  have hσ:σA=rawMarkedDeleteRims σ₀ (DR.comap f).edgeFinset:=rawMarkedRestrictPair_deleteRims f g σ DR
  have he (a b:W):R₀ a b↔R (f a) (f b):=by
    dsimp only [R₀,R,σ₀]
    rw [markedPhysicalRim_restrictPair_eq f g π ρ hf P d σ mark a b]
  have hv:=relation_two_step_vertex_restriction f.toEmbedding R x y
  have hv':|((Finset.univ.filter (fun z=>R₀ x z∧R₀ z y)).card:ℝ)-
      (Finset.univ.filter (fun z=>R (f x) z∧R z (f y))).card|≤(Finset.univ\Finset.univ.image f).card:=by
    simp only [he]
    convert hv using 1 <;> congr!
  have hd:=marked_rim_two_step_physical_deletion (P.comap f) ρ d σ₀ (DR.comap f) mark δ hDR x y
  have hd':|((Finset.univ.filter (fun z=>RA x z∧RA z y)).card:ℝ)-
      (Finset.univ.filter (fun z=>R₀ x z∧R₀ z y)).card|≤2*δ:=by
    convert hd using 1 <;> simp only [RA,R₀,hσ]
  have hl:=hlower (f x) (f y) (fun h=>hxy (f.injective h))
  simp only [markedSampleArc_indicator_iff]
  change lower-_ -2*δ≤((Finset.univ.filter (fun z=>RA x z∧RA z y)).card:ℝ)
  have hvlo:=(abs_le.mp hv').1
  have hdlo:=(abs_le.mp hd').1
  linarith only [hl,hvlo,hdlo]

end Oberwolfach
