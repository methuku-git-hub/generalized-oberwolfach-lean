module

public import Oberwolfach.MarkedReservedDegreeLoss
public import Oberwolfach.MarkedBalanceTermDegrees
public import Oberwolfach.MarkedBalanceTermRestriction
public import Oberwolfach.OccurrenceDegreeDeletion

@[expose] public section

/-! Deleted incidence tests are the actual deleted typed degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]

theorem relation_row_restriction_loss {A:Type} [Fintype A] (H P:A→Prop):
    (∑ a,if H a∧¬P a then (1:ℝ) else 0)=
      (∑ a,if H a then (1:ℝ) else 0)-(∑ a,if H a∧P a then (1:ℝ) else 0):=by
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h:H a <;> by_cases p:P a <;> simp [h,p]

theorem marked_deleted_term_degree_bounds (tail head:E→V) (ktail khead:K→V)
    (H₀ HK:V→U→Prop) (PE:E→Prop) (PK:K→Prop) (P:V→U→Prop) (D:ℝ)
    (hb:∀ (r:V⊕U) (j:Fin 6),
      (((markedBalanceTermSet tail head ktail khead H₀ HK r j).filter
        (fun a=>¬markedActiveRetained PE PK (fun x u=>H₀ x u∧P x u) (fun x u=>HK x u∧P x u) a)).card:ℝ)≤D):
    (∀ v,(∑ e,if ¬PE e∧tail e=v then (1:ℝ) else 0)≤D ∧
      (∑ e,if ¬PE e∧head e=v then (1:ℝ) else 0)≤D ∧
      (∑ e,if ¬PK e∧ktail e=v then (1:ℝ) else 0)≤D ∧
      (∑ e,if ¬PK e∧khead e=v then (1:ℝ) else 0)≤D ∧
      (∑ u,if H₀ v u∧¬(H₀ v u∧P v u) then (1:ℝ) else 0)≤D ∧
      (∑ u,if HK v u∧¬(HK v u∧P v u) then (1:ℝ) else 0)≤D) ∧
    (∀ u,(∑ v,if H₀ v u∧¬(H₀ v u∧P v u) then (1:ℝ) else 0)≤D ∧
      (∑ v,if HK v u∧¬(HK v u∧P v u) then (1:ℝ) else 0)≤D):=by
  let t':=fun e:{e//PE e}=>tail e.val
  let h':=fun e:{e//PE e}=>head e.val
  let kt':=fun e:{e//PK e}=>ktail e.val
  let kh':=fun e:{e//PK e}=>khead e.val
  let H₀':=fun x u=>H₀ x u∧P x u
  let HK':=fun x u=>HK x u∧P x u
  let A:=fun r j=>((markedBalanceTermSet tail head ktail khead H₀ HK r j).card:ℝ)
  let B:=fun r j=>((markedBalanceTermSet t' h' kt' kh' H₀' HK' r j).card:ℝ)
  have hdiff (r:V⊕U) (j:Fin 6):A r j-B r j≤D:=by
    have he:=markedBalanceTermSet_restriction_card (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (H₀:=H₀) (HK:=HK) PE PK P r j
    have he':B r j=(((markedBalanceTermSet tail head ktail khead H₀ HK r j).filter
        (markedActiveRetained PE PK H₀' HK')).card:ℝ):=by
      convert congrArg (fun n:ℕ=>(n:ℝ)) he using 1 <;> congr!
    have hc:=Finset.card_filter_add_card_filter_not
      (s:=markedBalanceTermSet tail head ktail khead H₀ HK r j) (markedActiveRetained PE PK H₀' HK')
    have hc':(((markedBalanceTermSet tail head ktail khead H₀ HK r j).filter
        (markedActiveRetained PE PK H₀' HK')).card:ℝ)+
      ((markedBalanceTermSet tail head ktail khead H₀ HK r j).filter
        (fun a=>¬markedActiveRetained PE PK H₀' HK' a)).card=A r j:=by
      dsimp only [A]
      exact_mod_cast hc
    have hh:=hb r j
    change _≤D at hh
    rw [he']
    linarith only [hh,hc']
  have hr (v:V):=
    And.intro (markedBalanceTermSet_row_degrees tail head ktail khead H₀ HK v)
      (markedBalanceTermSet_row_degrees t' h' kt' kh' H₀' HK' v)
  have hc (u:U):=
    And.intro (markedBalanceTermSet_hub_degrees tail head ktail khead H₀ HK u)
      (markedBalanceTermSet_hub_degrees t' h' kt' kh' H₀' HK' u)
  constructor
  · intro v
    obtain ⟨⟨a0,a1,a2,a3,a4,a5⟩,⟨b0,b1,b2,b3,b4,b5⟩⟩:=hr v
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · have he:(∑ e,if ¬PE e∧tail e=v then (1:ℝ) else 0)=A (Sum.inl v) 0-B (Sum.inl v) 0:=by
        calc
          _ = occurrenceDegree tail v-occurrenceDegree t' v:=by
            convert (occurrenceDegree_restriction_loss tail PE v).symm using 1 <;> congr!
          _ = _:=by
            congr 1
            · convert a0.symm using 1 <;> congr!
            · convert b0.symm using 1 <;> congr!
      rw [he]
      exact hdiff (Sum.inl v) 0
    · have he:(∑ e,if ¬PE e∧head e=v then (1:ℝ) else 0)=A (Sum.inl v) 2-B (Sum.inl v) 2:=by
        calc
          _ = occurrenceDegree head v-occurrenceDegree h' v:=by
            convert (occurrenceDegree_restriction_loss head PE v).symm using 1 <;> congr!
          _ = _:=by
            congr 1
            · convert a2.symm using 1 <;> congr!
            · convert b2.symm using 1 <;> congr!
      rw [he]
      exact hdiff (Sum.inl v) 2
    · have he:(∑ e,if ¬PK e∧ktail e=v then (1:ℝ) else 0)=A (Sum.inl v) 1-B (Sum.inl v) 1:=by
        calc
          _ = occurrenceDegree ktail v-occurrenceDegree kt' v:=by
            convert (occurrenceDegree_restriction_loss ktail PK v).symm using 1 <;> congr!
          _ = _:=by
            congr 1
            · convert a1.symm using 1 <;> congr!
            · convert b1.symm using 1 <;> congr!
      rw [he]
      exact hdiff (Sum.inl v) 1
    · have he:(∑ e,if ¬PK e∧khead e=v then (1:ℝ) else 0)=A (Sum.inl v) 3-B (Sum.inl v) 3:=by
        calc
          _ = occurrenceDegree khead v-occurrenceDegree kh' v:=by
            convert (occurrenceDegree_restriction_loss khead PK v).symm using 1 <;> congr!
          _ = _:=by
            congr 1
            · convert a3.symm using 1 <;> congr!
            · convert b3.symm using 1 <;> congr!
      rw [he]
      exact hdiff (Sum.inl v) 3
    · have he:(∑ u,if H₀ v u∧¬(H₀ v u∧P v u) then (1:ℝ) else 0)=A (Sum.inl v) 4-B (Sum.inl v) 4:=by
        have hsum:=relation_row_restriction_loss (H₀ v) (P v)
        calc
          _ = (∑ u,if H₀ v u∧¬P v u then (1:ℝ) else 0):=by
            apply Finset.sum_congr rfl;intro u _;by_cases hh:H₀ v u <;> simp [hh]
          _ = _:=by
            rw [hsum]
            congr 1
            · convert a4.symm using 1 <;> congr!
            · convert b4.symm using 1 <;> congr!
      rw [he]
      exact hdiff (Sum.inl v) 4
    · have he:(∑ u,if HK v u∧¬(HK v u∧P v u) then (1:ℝ) else 0)=A (Sum.inl v) 5-B (Sum.inl v) 5:=by
        have hsum:=relation_row_restriction_loss (HK v) (P v)
        calc
          _ = (∑ u,if HK v u∧¬P v u then (1:ℝ) else 0):=by
            apply Finset.sum_congr rfl;intro u _;by_cases hh:HK v u <;> simp [hh]
          _ = _:=by
            rw [hsum]
            congr 1
            · convert a5.symm using 1 <;> congr!
            · convert b5.symm using 1 <;> congr!
      rw [he]
      exact hdiff (Sum.inl v) 5
  · intro u
    obtain ⟨⟨a4,a5⟩,⟨b4,b5⟩⟩:=hc u
    constructor
    · have he:(∑ v,if H₀ v u∧¬(H₀ v u∧P v u) then (1:ℝ) else 0)=A (Sum.inr u) 4-B (Sum.inr u) 4:=by
        have hsum:=relation_row_restriction_loss (fun v=>H₀ v u) (fun v=>P v u)
        calc
          _ = (∑ v,if H₀ v u∧¬P v u then (1:ℝ) else 0):=by
            apply Finset.sum_congr rfl;intro v _;by_cases hh:H₀ v u <;> simp [hh]
          _ = _:=by
            rw [hsum]
            congr 1
            · convert a4.symm using 1 <;> congr!
            · convert b4.symm using 1 <;> congr!
      rw [he]
      exact hdiff (Sum.inr u) 4
    · have he:(∑ v,if HK v u∧¬(HK v u∧P v u) then (1:ℝ) else 0)=A (Sum.inr u) 5-B (Sum.inr u) 5:=by
        have hsum:=relation_row_restriction_loss (fun v=>HK v u) (fun v=>P v u)
        calc
          _ = (∑ v,if HK v u∧¬P v u then (1:ℝ) else 0):=by
            apply Finset.sum_congr rfl;intro v _;by_cases hh:HK v u <;> simp [hh]
          _ = _:=by
            rw [hsum]
            congr 1
            · convert a5.symm using 1 <;> congr!
            · convert b5.symm using 1 <;> congr!
      rw [he]
      exact hdiff (Sum.inr u) 5
end Oberwolfach
