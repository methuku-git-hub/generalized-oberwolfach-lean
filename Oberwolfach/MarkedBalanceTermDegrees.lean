module

public import Oberwolfach.MarkedBalanceTestSets
public import Oberwolfach.MarkedDeletedIncidence

@[expose] public section

/-! The fixed test sets are the actual six degree terms, with cardinalities
identified explicitly. This permits the probabilistic estimate to feed
the numerical near-balance packing theorem without a new balance assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]

theorem marked_balance_spoke_row_count (H₀ HK:V→U→Prop) (v:V) (j:Bool):
    ((Finset.univ.filter (fun z:{z:V×U//H₀ z.1 z.2∨HK z.1 z.2}=>
      z.val.1=v∧(if j then HK z.val.1 z.val.2 else H₀ z.val.1 z.val.2))).card:ℝ)=
      ∑ u,if (if j then HK v u else H₀ v u) then (1:ℝ) else 0:=by
  have h:=subtype_pair_filter_row (fun x u=>H₀ x u∨HK x u)
    (fun x u=>if j then HK x u else H₀ x u) v
  calc
    _ = ∑ u,if (H₀ v u∨HK v u)∧(if j then HK v u else H₀ v u) then (1:ℝ) else 0:=by
      convert h using 1 <;> congr!
    _ = _:=by
      apply Finset.sum_congr rfl
      intro u _
      cases j <;> by_cases h0:H₀ v u <;> by_cases hk:HK v u <;> simp [h0,hk]

theorem marked_balance_spoke_col_count (H₀ HK:V→U→Prop) (u:U) (j:Bool):
    ((Finset.univ.filter (fun z:{z:V×U//H₀ z.1 z.2∨HK z.1 z.2}=>
      z.val.2=u∧(if j then HK z.val.1 z.val.2 else H₀ z.val.1 z.val.2))).card:ℝ)=
      ∑ v,if (if j then HK v u else H₀ v u) then (1:ℝ) else 0:=by
  have h:=subtype_pair_filter_col (fun x u=>H₀ x u∨HK x u)
    (fun x u=>if j then HK x u else H₀ x u) u
  calc
    _ = ∑ v,if (H₀ v u∨HK v u)∧(if j then HK v u else H₀ v u) then (1:ℝ) else 0:=by
      convert h using 1 <;> congr!
    _ = _:=by
      apply Finset.sum_congr rfl
      intro v _
      cases j <;> by_cases h0:H₀ v u <;> by_cases hk:HK v u <;> simp [h0,hk]

theorem markedBalanceTermSet_row_degrees (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (v:V):
    let d:=fun j=>((markedBalanceTermSet tail head ktail khead H₀ HK (Sum.inl v) j).card:ℝ);
    d 0=occurrenceDegree tail v∧d 1=occurrenceDegree ktail v∧
    d 2=occurrenceDegree head v∧d 3=occurrenceDegree khead v∧
    d 4=(∑ u,if H₀ v u then (1:ℝ) else 0)∧d 5=(∑ u,if HK v u then (1:ℝ) else 0):=by
  intro d
  have hc (j:Fin 6):
      d j=(((Finset.univ.filter (fun e:E=>(j=0∧tail e=v)∨(j=2∧head e=v))).card:ℝ)+
        (Finset.univ.filter (fun e:K=>(j=1∧ktail e=v)∨(j=3∧khead e=v))).card)+
        (Finset.univ.filter (fun z:{z:V×U//H₀ z.1 z.2∨HK z.1 z.2}=>z.val.1=v∧
          ((j=4∧H₀ z.val.1 z.val.2)∨(j=5∧HK z.val.1 z.val.2)))).card:=by
    dsimp only [d,markedBalanceTermSet]
    rw [filter_card_sum_type,filter_card_sum_type]
    simp only [markedBalanceTerm,Sum.elim_inl,Sum.elim_inr,Nat.cast_add]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [hc];norm_num [occurrenceDegree]
    convert (Finset.sum_boole (R:=ℝ) (fun e=>tail e=v) Finset.univ).symm using 1 <;> congr!
  · rw [hc];norm_num [occurrenceDegree]
    convert (Finset.sum_boole (R:=ℝ) (fun e=>ktail e=v) Finset.univ).symm using 1 <;> congr!
  · rw [hc];norm_num [occurrenceDegree]
    convert (Finset.sum_boole (R:=ℝ) (fun e=>head e=v) Finset.univ).symm using 1 <;> congr!
  · rw [hc];norm_num [occurrenceDegree]
    convert (Finset.sum_boole (R:=ℝ) (fun e=>khead e=v) Finset.univ).symm using 1 <;> congr!
  · rw [hc];norm_num
    have h:=marked_balance_spoke_row_count H₀ HK v false
    norm_num at h
    convert h using 1 <;> congr!
  · rw [hc];norm_num
    have h:=marked_balance_spoke_row_count H₀ HK v true
    norm_num at h
    convert h using 1 <;> congr!

theorem markedBalanceTermSet_hub_degrees (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (u:U):
    ((markedBalanceTermSet tail head ktail khead H₀ HK (Sum.inr u) 4).card:ℝ)=
      (∑ v,if H₀ v u then (1:ℝ) else 0)∧
    ((markedBalanceTermSet tail head ktail khead H₀ HK (Sum.inr u) 5).card:ℝ)=
      (∑ v,if HK v u then (1:ℝ) else 0):=by
  constructor
  · unfold markedBalanceTermSet
    rw [filter_card_sum_type]
    simp only [markedBalanceTerm,Sum.elim_inl,Sum.elim_inr,Finset.filter_false,Finset.card_empty,zero_add]
    norm_num
    have h:=marked_balance_spoke_col_count H₀ HK u false
    norm_num at h
    convert h using 1 <;> congr!
  · unfold markedBalanceTermSet
    rw [filter_card_sum_type]
    simp only [markedBalanceTerm,Sum.elim_inl,Sum.elim_inr,Finset.filter_false,Finset.card_empty,zero_add]
    norm_num
    have h:=marked_balance_spoke_col_count H₀ HK u true
    norm_num at h
    convert h using 1 <;> congr!
end Oberwolfach
