module

public import Oberwolfach.MarkedPhysicalCutTransfer
public import Oberwolfach.BoundedMatrixVertexRestriction

@[expose] public section

/-! Degree estimates for the actual sampled arcs after restriction and
physical deletion. The original degree target is retained until the final
explicit comparison with the new target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem markedPhysicalRim_real_le_one (P:SimpleGraph V) (π:Equiv.Perm V) (b:ℕ)
    (σ:Sym2 V→Option (Bool×Bool)) (mark:Bool) (x y:V):
    |(markedPhysicalRim P π b σ mark x y:ℝ)|≤1:=by
  unfold markedPhysicalRim permutationSeparatedMatrix markedPhysicalOrientation
  split_ifs <;> norm_num <;> split_ifs <;> norm_num

theorem marked_rim_degree_physical_deletion
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (DR:SimpleGraph V) (mark:Bool) (x:V):
    let M:=markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark
    let M':=markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark;
    |(∑ y,(M' x y:ℝ))-(∑ y,(M x y:ℝ))|≤DR.degree x ∧
    |(∑ y,(M' y x:ℝ))-(∑ y,(M y x:ℝ))|≤DR.degree (if mark then π x else x):=by
  intro M M'
  have hr (incoming:Bool):
      |(∑ y,if rawMarkedPairRims P π d (rawMarkedDeleteRims σ DR.edgeFinset)
          (markedRowRim (mark,incoming,x) y) then (1:ℝ) else 0)-
        (∑ y,if rawMarkedPairRims P π d σ (markedRowRim (mark,incoming,x) y) then (1:ℝ) else 0)|≤
        DR.degree (if mark && incoming then π x else x):=
    (finset_indicator_sum_change Finset.univ _ _).trans
      (marked_row_rim_physical_deletion_change P π d σ DR Finset.univ (mark,incoming,x))
  have he (τ:RawMarkedOutcome V U Γ Color) (a b:V):
      (if markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark a b=1 then (1:ℝ) else 0)=
        (markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark a b:ℝ):=by
    exact_mod_cast markedPhysicalRim_indicator P π (3*d) (fun e=>τ (Sum.inl e)) mark a b
  constructor
  · cases mark <;> simpa [M,M',markedRowRim,rawMarkedPairRims,he] using hr false
  · cases mark <;> simpa [M,M',markedRowRim,rawMarkedPairRims,he] using hr true

theorem marked_protected_active_degrees
    (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (DR:SimpleGraph V)
    (target targetA:Bool→ℝ) (err δ:ℝ)
    (hDR:∀ x,((DR.comap f).degree x:ℝ)≤δ)
    (hout:∀ mark x,|(∑ y,(markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y:ℝ))-target mark|≤err)
    (hin:∀ mark x,|(∑ y,(markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark y x:ℝ))-target mark|≤err):
    let σA:=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset);
    ∀ mark x,
      |occurrenceDegree (fun e:MarkedSampleArc (P.comap f) ρ (3*d) (fun a=>σA (Sum.inl a)) mark=>e.val.1) x-targetA mark|≤
        err+(Finset.univ\Finset.univ.image f).card+δ+|target mark-targetA mark| ∧
      |occurrenceDegree (fun e:MarkedSampleArc (P.comap f) ρ (3*d) (fun a=>σA (Sum.inl a)) mark=>e.val.2) x-targetA mark|≤
        err+(Finset.univ\Finset.univ.image f).card+δ+|target mark-targetA mark|:=by
  intro σA mark x
  let σ₀:=rawMarkedRestrictPair f g σ
  let M:=markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark
  let M₀:=markedPhysicalRim (P.comap f) ρ (3*d) (fun e=>σ₀ (Sum.inl e)) mark
  let MA:=markedPhysicalRim (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) mark
  have hσ:σA=rawMarkedDeleteRims σ₀ (DR.comap f).edgeFinset:=rawMarkedRestrictPair_deleteRims f g σ DR
  have he (a b:W):M₀ a b=M (f a) (f b):=markedPhysicalRim_restrictPair_eq f g π ρ hf P d σ mark a b
  have hv:=bounded_matrix_vertex_restriction f.toEmbedding (fun a b=>(M a b:ℝ))
    (markedPhysicalRim_real_le_one P π (3*d) _ mark) x
  have hv':|(∑ y,(M₀ x y:ℝ))-(∑ y,(M (f x) y:ℝ))|≤(Finset.univ\Finset.univ.image f).card ∧
      |(∑ y,(M₀ y x:ℝ))-(∑ y,(M y (f x):ℝ))|≤(Finset.univ\Finset.univ.image f).card:=by
    simp only [he]
    convert hv using 1 <;> congr!
  have hd:=marked_rim_degree_physical_deletion (P.comap f) ρ d σ₀ (DR.comap f) mark x
  have hd':|(∑ y,(MA x y:ℝ))-(∑ y,(M₀ x y:ℝ))|≤δ ∧
      |(∑ y,(MA y x:ℝ))-(∑ y,(M₀ y x:ℝ))|≤δ:=by
    dsimp only [MA]
    rw [hσ]
    exact ⟨hd.1.trans (hDR x),hd.2.trans (hDR _)⟩
  have ht (a b c:ℝ) (h1:|a-b|≤δ) (h2:|b-c|≤(Finset.univ\Finset.univ.image f).card)
      (h3:|c-target mark|≤err):
      |a-targetA mark|≤err+(Finset.univ\Finset.univ.image f).card+δ+|target mark-targetA mark|:=by
    calc
      _ ≤ |a-b|+|b-c|+|c-target mark|+|target mark-targetA mark|:=by
        have h1':=abs_sub_le a b c
        have h2':=abs_sub_le a c (target mark)
        have h3':=abs_sub_le a (target mark) (targetA mark)
        linarith
      _ ≤ _:=by linarith
  have hdeg:=markedSampleArc_degrees (P.comap f) ρ (3*d) (fun a=>σA (Sum.inl a)) mark x
  rw [hdeg.1,hdeg.2,Nat.cast_sum,Nat.cast_sum]
  exact ⟨ht _ _ _ hd'.1 hv'.1 (hout mark (f x)),ht _ _ _ hd'.2 hv'.2 (hin mark (f x))⟩

end Oberwolfach
