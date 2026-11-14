module

public import Oberwolfach.MarkedBalanceInnerTerms

@[expose] public section

/-! All six degree terms at a fixed ambient root use one common restricted
host: only the opposite endpoint is restricted. This includes roots outside
the two fixed domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]

theorem markedBalanceTermSet_domain_card
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (X:Finset V) (Z:Finset U) (r:V⊕U) (j:Fin 6):
    let PE:E→Prop:=fun e=>match r with
      | Sum.inl v=>(if tail e=v then head e else tail e)∈X
      | Sum.inr _=>True
    let PK:K→Prop:=fun e=>match r with
      | Sum.inl v=>(if ktail e=v then khead e else ktail e)∈X
      | Sum.inr _=>True
    let P:V→U→Prop:=fun x u=>match r with
      | Sum.inl _=>u∈Z
      | Sum.inr _=>x∈X;
    ((markedBalanceTermSet tail head ktail khead H₀ HK r j).filter (fun e=>
      (if markedActiveAuxTail tail ktail H₀ HK e=r then markedActiveAuxHead head khead H₀ HK e
        else markedActiveAuxTail tail ktail H₀ HK e)∈ordinaryInnerVertices X Z)).card=
    (markedBalanceTermSet (fun e:{e:E//PE e}=>tail e.val) (fun e:{e:E//PE e}=>head e.val)
      (fun e:{e:K//PK e}=>ktail e.val) (fun e:{e:K//PK e}=>khead e.val)
      (fun x u=>H₀ x u∧P x u) (fun x u=>HK x u∧P x u) r j).card:=by
  intro PE PK P
  rw [markedBalanceTermSet_restriction_card PE PK P]
  congr 1
  apply Finset.filter_congr
  intro a ha
  have ht:markedBalanceTerm tail head ktail khead H₀ HK r j a:=(Finset.mem_filter.mp ha).2
  rcases r with v|u <;> rcases a with (e|e)|s
  · simp only [markedActiveAuxTail,markedActiveAuxHead,Sum.elim_inl,Sum.inl.injEq,
      markedActiveRetained,PE]
    split_ifs <;> simp only [ordinaryInnerVertices_left]
  · simp only [markedActiveAuxTail,markedActiveAuxHead,Sum.elim_inl,Sum.elim_inr,Sum.inl.injEq,
      markedActiveRetained,PK]
    split_ifs <;> simp only [ordinaryInnerVertices_left]
  · change s.val.1=v∧_ at ht
    have hs:=s.property
    simp only [markedActiveAuxTail,markedActiveAuxHead,Sum.elim_inr,ht.1,ite_true,
      ordinaryInnerVertices_right,markedActiveRetained,P]
    rw [ht.1] at hs
    tauto
  · exact ht.elim
  · exact ht.elim
  · change s.val.2=u∧_ at ht
    have hs:=s.property
    simp only [markedActiveAuxTail,markedActiveAuxHead,Sum.elim_inr,Sum.inl_ne_inr,ite_false,
      ordinaryInnerVertices_left,markedActiveRetained,P]
    tauto

end Oberwolfach
