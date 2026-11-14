module

public import Oberwolfach.MarkedMatrixCorrectionRemainder

@[expose] public section

/-! Bounds on the actual finite edge sets selected by the four correction
matrices. The original occurrence identifiers and spoke types are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K : Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]

theorem marked_matrix_deleted_arc_incidence
    (tail head:E→V) (ktail khead:K→V)
    (hinj:Function.Injective (fun e=>(tail e,head e)))
    (hkinj:Function.Injective (fun e=>(ktail e,khead e)))
    (J₀ Jₖ:V→V→ℕ)
    (hJ₀:∀ x y,J₀ x y≤occurrenceMultiplicity tail head x y)
    (hJₖ:∀ x y,Jₖ x y≤occurrenceMultiplicity ktail khead x y)
    (v:V):
    let A:=Finset.univ.filter (Sum.elim (fun e=>J₀ (tail e) (head e)≠0) (fun e=>Jₖ (ktail e) (khead e)≠0))
    ((A.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤
      (∑ x,(J₀ v x:ℝ))+(∑ x,(J₀ x v:ℝ))+(∑ x,(Jₖ v x:ℝ))+(∑ x,(Jₖ x v:ℝ)):=by
  intro A
  have he (Z:Type) [Fintype Z] (t h:Z→V) (J:V→V→ℕ):
      (∑ e:Z, if J (t e) (h e)≠0∧(v=t e∨v=h e) then (1:ℝ) else 0)≤
        (∑ e:Z,if J (t e) (h e)≠0∧t e=v then (1:ℝ) else 0)+
        (∑ e:Z,if J (t e) (h e)≠0∧h e=v then (1:ℝ) else 0):=by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro e _
    by_cases hj:J (t e) (h e)=0 <;> by_cases ht:t e=v <;> by_cases hh:h e=v <;> simp_all <;> norm_num
    simp [Ne.symm ht,Ne.symm hh]
  have h0:=he E tail head J₀
  have hk:=he K ktail khead Jₖ
  rw [occurrence_matrix_deleted_degree tail head hinj J₀ hJ₀,
    occurrence_matrix_deleted_indegree tail head hinj J₀ hJ₀] at h0
  rw [occurrence_matrix_deleted_degree ktail khead hkinj Jₖ hJₖ,
    occurrence_matrix_deleted_indegree ktail khead hkinj Jₖ hJₖ] at hk
  have hf:(A.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a))=
      Finset.univ.filter (fun a:E⊕K=>
        Sum.elim (fun e=>J₀ (tail e) (head e)≠0) (fun e=>Jₖ (ktail e) (khead e)≠0) a∧
        (v=Sum.elim tail ktail a∨v=Sum.elim head khead a)):=by
    ext a;simp only [A,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [hf]
  simp only [Finset.card_filter,Nat.cast_add,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
    Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
  linarith only [h0,hk]

theorem marked_matrix_deleted_spoke_degrees
    (H₀ HK:V→U→Prop) (L₀ Lₖ:V→U→ℕ)
    :
    let S:=Finset.univ.filter (fun z:V×U=>(H₀ z.1 z.2∧L₀ z.1 z.2≠0)∨(HK z.1 z.2∧Lₖ z.1 z.2≠0))
    (∀ v,((S.filter (fun z=>v=z.1)).card:ℝ)≤(∑ u,(L₀ v u:ℝ))+(∑ u,(Lₖ v u:ℝ)))∧
    (∀ u,((S.filter (fun z=>z.2=u)).card:ℝ)≤(∑ v,(L₀ v u:ℝ))+(∑ v,(Lₖ v u:ℝ))):=by
  intro S
  have he (v:V) (u:U):
      (if (H₀ v u∧L₀ v u≠0)∨(HK v u∧Lₖ v u≠0) then (1:ℝ) else 0)≤(L₀ v u:ℝ)+(Lₖ v u:ℝ):=by
    split_ifs with hh
    · rcases hh with hh|hh
      · have hn:1≤L₀ v u:=Nat.one_le_iff_ne_zero.mpr hh.2
        have hr:(1:ℝ)≤L₀ v u:=by exact_mod_cast hn
        linarith only [hr,(Nat.cast_nonneg (Lₖ v u):(0:ℝ)≤Lₖ v u)]
      · have hn:1≤Lₖ v u:=Nat.one_le_iff_ne_zero.mpr hh.2
        have hr:(1:ℝ)≤Lₖ v u:=by exact_mod_cast hn
        linarith only [hr,(Nat.cast_nonneg (L₀ v u):(0:ℝ)≤L₀ v u)]
    · positivity
  constructor
  · intro v
    have hf:S.filter (fun z=>v=z.1)=Finset.univ.filter (fun z:V×U=>
        ((H₀ z.1 z.2∧L₀ z.1 z.2≠0)∨(HK z.1 z.2∧Lₖ z.1 z.2≠0))∧z.1=v):=by
      ext z;simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,eq_comm]
    rw [hf]
    have hc:(Finset.univ.filter (fun z:V×U=>
        ((H₀ z.1 z.2∧L₀ z.1 z.2≠0)∨(HK z.1 z.2∧Lₖ z.1 z.2≠0))∧z.1=v)).card=
        (Finset.univ.filter (fun u=>(H₀ v u∧L₀ v u≠0)∨(HK v u∧Lₖ v u≠0))).card:=by
      convert finite_relation_row_card (fun v u=>(H₀ v u∧L₀ v u≠0)∨(HK v u∧Lₖ v u≠0)) v using 1 <;> congr!
    rw [hc]
    simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun u _=>he v u)
  · intro u
    have hf:S.filter (fun z=>z.2=u)=Finset.univ.filter (fun z:V×U=>
        ((H₀ z.1 z.2∧L₀ z.1 z.2≠0)∨(HK z.1 z.2∧Lₖ z.1 z.2≠0))∧z.2=u):=by
      ext z;simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [hf]
    have hc:(Finset.univ.filter (fun z:V×U=>
        ((H₀ z.1 z.2∧L₀ z.1 z.2≠0)∨(HK z.1 z.2∧Lₖ z.1 z.2≠0))∧z.2=u)).card=
        (Finset.univ.filter (fun v=>(H₀ v u∧L₀ v u≠0)∨(HK v u∧Lₖ v u≠0))).card:=by
      convert finite_relation_col_card (fun v u=>(H₀ v u∧L₀ v u≠0)∨(HK v u∧Lₖ v u≠0)) u using 1 <;> congr!
    rw [hc]
    simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun v _=>he v u)

end Oberwolfach
