module

public import Oberwolfach.MarkedBalanceTermRestriction

@[expose] public section

/-! The inner-neighbour term retains all ambient roots. For an outgoing
arc its head is restricted, for an incoming arc its tail is restricted;
spoke rows use the inner hub set and spoke columns the inner row set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]

theorem opposite_endpoint_of_right {A:Type} [DecidableEq A] (x y r:A) (h:y=r):
    (if x=r then y else x)=x:=by subst y;split_ifs with h;exact h.symm;rfl

theorem marked_balance_inner_term_restriction
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (X:Finset V) (Z:Finset U) (r:V⊕U) (j:Fin 6):
    let PE:E→Prop:=fun e=>match r with
      | Sum.inl _=>(if j=0 then head e else tail e)∈X
      | Sum.inr _=>True
    let PK:K→Prop:=fun e=>match r with
      | Sum.inl _=>(if j=1 then khead e else ktail e)∈X
      | Sum.inr _=>True
    let P:V→U→Prop:=fun x u=>match r with
      | Sum.inl _=>u∈Z
      | Sum.inr _=>x∈X;
    ((markedBalanceTermSet tail head ktail khead H₀ HK r j).filter (fun e=>
      (if markedActiveAuxTail tail ktail H₀ HK e=r then markedActiveAuxHead head khead H₀ HK e
        else markedActiveAuxTail tail ktail H₀ HK e)∈ordinaryInnerVertices X Z)).card=
    (markedBalanceTermSet (V:=V) (U:=U) (E:={e:E//PE e}) (K:={e:K//PK e}) (fun e:{e:E//PE e}=>tail e.val) (fun e:{e:E//PE e}=>head e.val)
      (fun e:{e:K//PK e}=>ktail e.val) (fun e:{e:K//PK e}=>khead e.val)
      (fun x u=>H₀ x u∧P x u) (fun x u=>HK x u∧P x u) r j).card:=by
  intro PE PK P
  rw [markedBalanceTermSet_restriction_card PE PK P]
  congr 1
  apply Finset.filter_congr
  intro a ha
  have ht:markedBalanceTerm tail head ktail khead H₀ HK r j a:=(Finset.mem_filter.mp ha).2
  rcases r with v|u <;> rcases a with (e|e)|z
  · change (j=0∧tail e=v)∨(j=2∧head e=v) at ht
    rcases ht with ⟨hj,ht⟩|⟨hj,hh⟩
    · subst j
      simp only [markedActiveAuxTail,markedActiveAuxHead,Sum.elim_inl,ht,ite_true,
        ordinaryInnerVertices_left,markedActiveRetained,PE]
    · subst j
      have he:=(opposite_endpoint_of_right (Sum.inl (tail e):V⊕U) (Sum.inl (head e)) (Sum.inl v) (congrArg Sum.inl hh))
      simp only [markedActiveAuxTail,markedActiveAuxHead,Sum.elim_inl,he,
        ordinaryInnerVertices_left,markedActiveRetained,PE]
      norm_num
  · change (j=1∧ktail e=v)∨(j=3∧khead e=v) at ht
    rcases ht with ⟨hj,ht⟩|⟨hj,hh⟩
    · subst j
      simp only [markedActiveAuxTail,markedActiveAuxHead,Sum.elim_inl,Sum.elim_inr,ht,ite_true,
        ordinaryInnerVertices_left,markedActiveRetained,PK]
    · subst j
      have he:=(opposite_endpoint_of_right (Sum.inl (ktail e):V⊕U) (Sum.inl (khead e)) (Sum.inl v) (congrArg Sum.inl hh))
      simp only [markedActiveAuxTail,markedActiveAuxHead,Sum.elim_inl,Sum.elim_inr,he,
        ordinaryInnerVertices_left,markedActiveRetained,PK]
      norm_num
  · change z.val.1=v∧_ at ht
    have hp:=z.property
    rw [ht.1] at hp
    simp only [markedActiveAuxTail,markedActiveAuxHead,Sum.elim_inr,ht.1,ite_true,
      ordinaryInnerVertices_right,markedActiveRetained,P]
    tauto
  · exact ht.elim
  · exact ht.elim
  · change z.val.2=u∧_ at ht
    have hp:=z.property
    simp only [markedActiveAuxTail,markedActiveAuxHead,Sum.elim_inr,Sum.inl_ne_inr,ite_false,
      ordinaryInnerVertices_left,markedActiveRetained,P]
    tauto
end Oberwolfach
