module

public import Oberwolfach.TypedMatrixRealization
public import Oberwolfach.MarkedRemainderSubhost
public import Oberwolfach.MarkedIncidentResources

@[expose] public section

/-! The matrix balances used by sparse correction imply the four finite
remainder identities used by terminal absorption. Spoke types are kept
disjoint, rather than counting a spoke twice in the finite resource set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem finite_relation_row_card (H:V→U→Prop) (v:V):
    (Finset.univ.filter (fun z:V×U=>H z.1 z.2∧z.1=v)).card=
      (Finset.univ.filter (H v)).card:=by
  simp only [Finset.card_filter,Fintype.sum_prod_type]
  have he (x:V) (u:U):(if H x u∧x=v then (1:ℕ) else 0)=
      if x=v then (if H v u then 1 else 0) else 0:=by
    by_cases hx:x=v <;> simp_all
  simp_rw [he]
  simp

theorem finite_relation_col_card (H:V→U→Prop) (u:U):
    (Finset.univ.filter (fun z:V×U=>H z.1 z.2∧z.2=u)).card=
      (Finset.univ.filter (fun v=>H v u)).card:=by
  simp only [Finset.card_filter,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  have he (y:U):(if H v y∧y=u then (1:ℕ) else 0)=
      if y=u then (if H v u then 1 else 0) else 0:=by
    by_cases hy:y=u <;> simp_all
  simp only [he]
  simp

theorem occurrence_degree_eq_filter_card {A:Type} [Fintype A] (f:A→V) (v:V):
    occurrenceDegree f v=((Finset.univ.filter (fun a=>f a=v)).card:ℝ):=by
  simp only [occurrenceDegree,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  congr!

theorem marked_matrix_balanced_divisible
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (m:ℕ)
    (hH:∀ v u,¬(H₀ v u∧HK v u))
    (hbal:TypedMatrixBalanced m (occurrenceMultiplicity tail head) (occurrenceMultiplicity ktail khead)
      (relationMultiplicity H₀) (relationMultiplicity HK)):
    MarkedRemainderDivisible tail head ktail khead HK Finset.univ
      (Finset.univ.filter (fun z:V×U=>H₀ z.1 z.2∨HK z.1 z.2)) m:=by
  let S:=Finset.univ.filter (fun z:V×U=>H₀ z.1 z.2∨HK z.1 z.2)
  obtain ⟨hdir,hmark,hrow,hhub⟩:=typed_matrix_balanced_occurrence_degrees m tail head ktail khead H₀ HK hbal
  have hSrow (v:V):((S.filter (fun z=>z.1=v)).card:ℝ)=
      (∑ u,if H₀ v u then (1:ℝ) else 0)+(∑ u,if HK v u then (1:ℝ) else 0):=by
    have he:S.filter (fun z=>z.1=v)=Finset.univ.filter (fun z:V×U=>(H₀ z.1 z.2∨HK z.1 z.2)∧z.1=v):=by
      ext z;simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
    have hh:(Finset.univ.filter (fun z:V×U=>(H₀ z.1 z.2∨HK z.1 z.2)∧z.1=v)).card=
        (Finset.univ.filter (fun u=>H₀ v u∨HK v u)).card:=by
      convert finite_relation_row_card (fun v u=>H₀ v u∨HK v u) v using 1 <;> congr!
    rw [he,hh]
    simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    have h:=hH v u
    by_cases h0:H₀ v u <;> by_cases hk:HK v u <;> simp_all
  have hSmark (v:V):((S.filter (fun z=>z.1=v∧HK z.1 z.2)).card:ℝ)=
      ∑ u,if HK v u then (1:ℝ) else 0:=by
    have he:S.filter (fun z=>z.1=v∧HK z.1 z.2)=Finset.univ.filter (fun z:V×U=>HK z.1 z.2∧z.1=v):=by
      ext z;simp only [S,Finset.mem_filter,Finset.mem_univ,true_and];tauto
    rw [he,finite_relation_row_card]
    simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  have hcolK (u:U):((S.filter (fun z=>z.2=u∧HK z.1 z.2)).card:ℝ)=
      ∑ v,if HK v u then (1:ℝ) else 0:=by
    have he:S.filter (fun z=>z.2=u∧HK z.1 z.2)=Finset.univ.filter (fun z:V×U=>HK z.1 z.2∧z.2=u):=by
      ext z;simp only [S,Finset.mem_filter,Finset.mem_univ,true_and];tauto
    rw [he,finite_relation_col_card]
    simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  have hcol0 (u:U):((S.filter (fun z=>z.2=u∧¬HK z.1 z.2)).card:ℝ)=
      ∑ v,if H₀ v u then (1:ℝ) else 0:=by
    have he:S.filter (fun z=>z.2=u∧¬HK z.1 z.2)=Finset.univ.filter (fun z:V×U=>H₀ z.1 z.2∧z.2=u):=by
      ext z
      have h:=hH z.1 z.2
      simp only [S,Finset.mem_filter,Finset.mem_univ,true_and];tauto
    rw [he,finite_relation_col_card]
    simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  constructor
  · intro v
    have hh:=hdir v
    simp only [occurrence_degree_eq_filter_card] at hh
    exact_mod_cast hh.symm
  · intro v
    have hh:((Finset.univ.filter (fun a:E⊕K=>Sum.elim head khead a=v)).card:ℝ)=
        ((S.filter (fun z=>z.1=v)).card:ℝ):=by
      rw [←occurrence_degree_eq_filter_card,←hdir v,hrow v,hSrow]
    exact_mod_cast hh
  · intro v
    have he:(Finset.univ.filter (fun a:E⊕K=>Sum.elim head khead a=v∧markedArcType a=true)).card=
        (Finset.univ.filter (fun a:K=>khead a=v)).card:=by
      simp only [Finset.card_filter,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,markedArcType,
        Bool.false_eq_true,and_false,ite_false,Finset.sum_const_zero,Bool.true_eq,and_true,zero_add]
    have hh:((Finset.univ.filter (fun a:E⊕K=>Sum.elim head khead a=v∧markedArcType a=true)).card:ℝ)=
        ((S.filter (fun z=>z.1=v∧HK z.1 z.2)).card:ℝ):=by
      rw [he,←occurrence_degree_eq_filter_card,hmark v,hSmark]
    exact_mod_cast hh
  · intro u
    have hh:((S.filter (fun z=>z.2=u∧¬HK z.1 z.2)).card:ℝ)=
        (m:ℝ)*(S.filter (fun z=>z.2=u∧HK z.1 z.2)).card:=by
      rw [hcol0,hcolK,hhub]
    exact_mod_cast hh

end Oberwolfach
