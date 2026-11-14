module

public import Oberwolfach.OccurrenceRelationMultiplicity
public import Oberwolfach.BipartiteNormalizedCutDeletion
public import Oberwolfach.DirectedRelationDeletion
public import Oberwolfach.OccurrenceMatrixDeletion

@[expose] public section

/-! Cut bounds for the actual retained occurrence host. The error is the
realized number of deleted incident occurrences; no retention probability
is applied to it. The cutoff for large cuts remains unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E:Type} [Fintype V] [Fintype E] [DecidableEq V]

theorem bipartiteLargeCut_coefficient_mono {X Y:Type} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (A:X→Y→ℕ) (δ h h':ℝ) (hh:h'≤h)
    (ha:BipartiteLargeCut A δ h):BipartiteLargeCut A δ h':=by
  intro S T hST
  apply le_trans _ (ha S T hST)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hh (by positivity)) (by positivity)) (by positivity)

theorem bipartiteLargeCut_subrelation (X Y:Type) [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (hn:0<Fintype.card X) (hm:0<Fintype.card Y)
    (P Q:X→Y→Prop) (hsub:∀ x y,Q x y→P x y) (δ h ζ:ℝ) (hζ:0≤ζ)
    (hrow:∀ x,(∑ y,if P x y∧¬Q x y then (1:ℝ) else 0)≤ζ*Fintype.card Y)
    (hcol:∀ y,(∑ x,if P x y∧¬Q x y then (1:ℝ) else 0)≤ζ*Fintype.card X)
    (hcut:BipartiteLargeCut (relationMultiplicity P) δ h):
    BipartiteLargeCut (relationMultiplicity Q) δ (h-ζ):=by
  have he (x:X) (y:Y):¬(P x y↔Q x y)↔P x y∧¬Q x y:=by have hs:=hsub x y;tauto
  exact bipartiteLargeCut_after_relation_changes hn hm P Q δ h ζ hζ
    (by simpa only [he] using hrow) (by simpa only [he] using hcol) hcut

theorem occurrence_relation_restriction_change (tail head:E→V) (P:E→Prop) (d:ℝ)
    (hout:∀ x,(∑ e,if ¬P e∧tail e=x then (1:ℝ) else 0)≤d)
    (hin:∀ y,(∑ e,if ¬P e∧head e=y then (1:ℝ) else 0)≤d):
    (∀ x,(∑ y,if ¬((∃ e,tail e=x∧head e=y)↔
        (∃ e:{e//P e},tail e.val=x∧head e.val=y)) then (1:ℝ) else 0)≤d)∧
    (∀ y,(∑ x,if ¬((∃ e,tail e=x∧head e=y)↔
        (∃ e:{e//P e},tail e.val=x∧head e.val=y)) then (1:ℝ) else 0)≤d):=by
  have he (x y:V):¬((∃ e,tail e=x∧head e=y)↔
      (∃ e:{e//P e},tail e.val=x∧head e.val=y))↔
      (∃ e,tail e=x∧head e=y)∧¬(∃ e:{e//P e},tail e.val=x∧head e.val=y):=by
    have hs:(∃ e:{e//P e},tail e.val=x∧head e.val=y)→∃ e,tail e=x∧head e=y:=by
      rintro ⟨e,he⟩;exact ⟨e.val,he⟩
    have hi {a b:Prop} (h:b→a):¬(a↔b)↔a∧¬b:=by tauto
    exact hi hs
  constructor
  · intro x
    simp only [he]
    convert (represented_relation_lost_outdegree tail head P x).trans (by convert hout x using 1 <;> congr!) using 1 <;> simp only [bipAdj] <;> congr!
  · intro y
    simp only [he]
    convert (represented_relation_lost_indegree tail head P y).trans (by convert hin y using 1 <;> congr!) using 1 <;> simp only [bipAdj] <;> congr!

theorem occurrence_bipartiteLargeCut_restriction (hn:0<Fintype.card V)
    (tail head:E→V) (hinj:Function.Injective (fun e=>(tail e,head e))) (P:E→Prop)
    (δ h ζ:ℝ) (hζ:0≤ζ)
    (hout:∀ x,(∑ e,if ¬P e∧tail e=x then (1:ℝ) else 0)≤ζ*Fintype.card V)
    (hin:∀ y,(∑ e,if ¬P e∧head e=y then (1:ℝ) else 0)≤ζ*Fintype.card V)
    (hcut:BipartiteLargeCut (occurrenceMultiplicity tail head) δ h):
    BipartiteLargeCut (occurrenceMultiplicity (fun e:{e//P e}=>tail e.val)
      (fun e=>head e.val)) δ (h-ζ):=by
  have hi:Function.Injective (fun e:{e//P e}=>(tail e.val,head e.val)):=by
    intro e f h;exact Subtype.ext (hinj h)
  rw [occurrenceMultiplicity_eq_relation tail head hinj] at hcut
  rw [occurrenceMultiplicity_eq_relation _ _ hi]
  obtain ⟨hr,hc⟩:=occurrence_relation_restriction_change tail head P (ζ*Fintype.card V) hout hin
  apply bipartiteLargeCut_after_relation_changes hn hn _ _ δ h ζ hζ
  · convert hr using 1 <;> congr!
  · convert hc using 1 <;> congr!
  · convert hcut using 1 <;> congr!

theorem occurrence_cut_restriction_loss (hn:0<Fintype.card V)
    (tail head:E→V) (hinj:Function.Injective (fun e=>(tail e,head e))) (P:E→Prop)
    (d:ℝ) (hd:0≤d)
    (hout:∀ x,(∑ e,if ¬P e∧tail e=x then (1:ℝ) else 0)≤d)
    (hin:∀ y,(∑ e,if ¬P e∧head e=y then (1:ℝ) else 0)≤d) (S T:Finset V):
    ((Finset.univ.filter (fun e=>tail e∈S∧head e∈T)).card:ℝ)-d*min (S.card:ℝ) T.card≤
    ((Finset.univ.filter (fun e:{e//P e}=>tail e.val∈S∧head e.val∈T)).card:ℝ):=by
  have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hi:Function.Injective (fun e:{e//P e}=>(tail e.val,head e.val)):=by
    intro e f h;exact Subtype.ext (hinj h)
  obtain ⟨hr,hc⟩:=occurrence_relation_restriction_change tail head P d hout hin
  have he:(d/(Fintype.card V:ℝ))*Fintype.card V=d:=div_mul_cancel₀ _ hnR.ne'
  have hh:=bipartite_cut_change_degrees (fun x y=>∃ e,tail e=x∧head e=y)
    (fun x y=>∃ e:{e//P e},tail e.val=x∧head e.val=y) (d/Fintype.card V)
    (by positivity) (by rw [he];convert hr using 1 <;> congr!) (by rw [he];convert hc using 1 <;> congr!) S T
  have hc0 (f g:E→V):matrixCut (occurrenceMultiplicity f g) S T=
      bipartiteMatrixCut (occurrenceMultiplicity f g) S T:=rfl
  have hscale:(d/(Fintype.card V:ℝ))*min ((Fintype.card V:ℝ)*S.card) ((Fintype.card V:ℝ)*T.card)=
      d*min (S.card:ℝ) T.card:=by
    rw [←mul_min_of_nonneg _ _ hnR.le,←mul_assoc,he]
  rw [hscale] at hh
  have hc0':bipartiteMatrixCut (fun x y=>if ∃ e,tail e=x∧head e=y then 1 else 0) S T=
      (Finset.univ.filter (fun e=>tail e∈S∧head e∈T)).card:=by
    rw [←occurrence_matrix_cut tail head, hc0]
    rw [occurrenceMultiplicity_eq_relation tail head hinj]
    congr! <;> simp only [relationMultiplicity] <;> congr!
  have hc1':bipartiteMatrixCut (fun x y=>if ∃ e:{e//P e},tail e.val=x∧head e.val=y then 1 else 0) S T=
      (Finset.univ.filter (fun e:{e//P e}=>tail e.val∈S∧head e.val∈T)).card:=by
    rw [←occurrence_matrix_cut (fun e:{e//P e}=>tail e.val) (fun e=>head e.val)]
    change _=bipartiteMatrixCut _ S T
    rw [occurrenceMultiplicity_eq_relation _ _ hi]
    congr! <;> simp only [relationMultiplicity] <;> congr!
  have hh':|((Finset.univ.filter (fun e:{e//P e}=>tail e.val∈S∧head e.val∈T)).card:ℝ)-
      (Finset.univ.filter (fun e=>tail e∈S∧head e∈T)).card|≤d*min (S.card:ℝ) T.card:=by
    rw [←hc0',←hc1']
    convert hh using 1 <;> congr!
  linarith only [(abs_le.mp hh').1]
end Oberwolfach
