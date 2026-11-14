module

public import Oberwolfach.MarkedFiniteFullBalanceBridge
public import Oberwolfach.MarkedFiniteSubtypeBalance
public import Oberwolfach.MarkedBalanceDomainTerms

@[expose] public section

/-! The inner balance inputs of approximate packing are the same finite
opposite-endpoint balance values used in the protected deletion calculation.
The root ranges remain the full ambient row and hub sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem markedFiniteDomainBalance_row
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (hd:∀ v u,¬(H₀ v u∧HK v u)) (m:ℕ) (X:Finset V) (Z:Finset U) (v:V) (i:Fin 3):
    markedFiniteDomainBalance tail head ktail khead HK Finset.univ
      (Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)) m X Z (Sum.inl v) i.castSucc=
    markedSixDegreeBalance m (fun j=>(((markedBalanceTermSet tail head ktail khead H₀ HK (Sum.inl v) j).filter
      (fun a=>(if markedActiveAuxTail tail ktail H₀ HK a=Sum.inl v then markedActiveAuxHead head khead H₀ HK a
        else markedActiveAuxTail tail ktail H₀ HK a)∈ordinaryInnerVertices X Z)).card:ℝ)) i.castSucc:=by
  let PE:E→Prop:=fun e=>(if tail e=v then head e else tail e)∈X
  let PK:K→Prop:=fun e=>(if ktail e=v then khead e else ktail e)∈X
  let P:V→U→Prop:=fun _ u=>u∈Z
  have hA:(Finset.univ.filter (Sum.elim PE PK))=
      (Finset.univ.filter (fun a:E⊕K=>(if Sum.elim tail ktail a=v then Sum.elim head khead a else Sum.elim tail ktail a)∈X)):=by
    apply Finset.filter_congr
    intro a _;cases a <;> rfl
  letI : Fintype {e:E//PE e}:=@Subtype.fintype E PE (fun e=>Classical.propDecidable (PE e)) inferInstance
  letI : Fintype {e:K//PK e}:=@Subtype.fintype K PK (fun e=>Classical.propDecidable (PK e)) inferInstance
  have hfin:=markedFiniteBalance_subtype_restriction tail head ktail khead H₀ HK PE PK P m (Sum.inl v) i.castSucc
  rw [hA] at hfin
  have hraw:=markedFiniteBalance_full_row
    (fun a:{e:E//PE e}=>tail a.val) (fun a:{e:E//PE e}=>head a.val)
    (fun a:{e:K//PK e}=>ktail a.val) (fun a:{e:K//PK e}=>khead a.val)
    (fun x u=>H₀ x u∧P x u) (fun x u=>HK x u∧P x u)
    (fun x u h=>hd x u ⟨h.1.1,h.2.1⟩) m v i
  calc
    _ = markedFiniteBalance (fun a:{e:E//PE e}=>tail a.val) (fun a:{e:E//PE e}=>head a.val)
      (fun a:{e:K//PK e}=>ktail a.val) (fun a:{e:K//PK e}=>khead a.val)
      (fun x u=>HK x u∧P x u) Finset.univ
      (Finset.univ.filter (fun s:V×U=>(H₀ s.1 s.2∧P s.1 s.2)∨(HK s.1 s.2∧P s.1 s.2))) m (Sum.inl v) i.castSucc:=by
        dsimp only [markedFiniteDomainBalance]
        convert hfin.symm using 1 <;> congr!
    _ = markedSixDegreeBalance m
      (fun j=>((markedBalanceTermSet (fun a:{e:E//PE e}=>tail a.val) (fun a:{e:E//PE e}=>head a.val)
        (fun a:{e:K//PK e}=>ktail a.val) (fun a:{e:K//PK e}=>khead a.val)
        (fun x u=>H₀ x u∧P x u) (fun x u=>HK x u∧P x u) (Sum.inl v) j).card:ℝ)) i.castSucc:=by
        convert hraw using 1 <;> congr!
    _ = _:=by
      apply congrArg (fun d:Fin 6→ℝ=>markedSixDegreeBalance m d i.castSucc)
      funext j
      have h:=markedBalanceTermSet_domain_card tail head ktail khead H₀ HK X Z (Sum.inl v) j
      convert congrArg (fun n:ℕ=>(n:ℝ)) h.symm using 1 <;> congr!

theorem markedFiniteDomainBalance_hub
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (hd:∀ v u,¬(H₀ v u∧HK v u)) (m:ℕ) (X:Finset V) (Z:Finset U) (u:U):
    markedFiniteDomainBalance tail head ktail khead HK Finset.univ
      (Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)) m X Z (Sum.inr u) 3=
    markedSixDegreeBalance m (fun j=>(((markedBalanceTermSet tail head ktail khead H₀ HK (Sum.inr u) j).filter
      (fun a=>(if markedActiveAuxTail tail ktail H₀ HK a=Sum.inr u then markedActiveAuxHead head khead H₀ HK a
        else markedActiveAuxTail tail ktail H₀ HK a)∈ordinaryInnerVertices X Z)).card:ℝ)) 3:=by
  let PE:E→Prop:=fun _=>True
  let PK:K→Prop:=fun _=>True
  let P:V→U→Prop:=fun x _=>x∈X
  letI : Fintype {e:E//PE e}:=@Subtype.fintype E PE (fun e=>Classical.propDecidable (PE e)) inferInstance
  letI : Fintype {e:K//PK e}:=@Subtype.fintype K PK (fun e=>Classical.propDecidable (PK e)) inferInstance
  have hfin:=markedFiniteBalance_subtype_restriction tail head ktail khead H₀ HK PE PK P m (Sum.inr u) 3
  have hraw:=markedFiniteBalance_full_hub
    (fun a:{e:E//PE e}=>tail a.val) (fun a:{e:E//PE e}=>head a.val)
    (fun a:{e:K//PK e}=>ktail a.val) (fun a:{e:K//PK e}=>khead a.val)
    (fun x u=>H₀ x u∧P x u) (fun x u=>HK x u∧P x u)
    (fun x u h=>hd x u ⟨h.1.1,h.2.1⟩) m u
  calc
    _ = markedFiniteBalance (fun a:{e:E//PE e}=>tail a.val) (fun a:{e:E//PE e}=>head a.val)
      (fun a:{e:K//PK e}=>ktail a.val) (fun a:{e:K//PK e}=>khead a.val)
      (fun x u=>HK x u∧P x u) Finset.univ
      (Finset.univ.filter (fun s:V×U=>(H₀ s.1 s.2∧P s.1 s.2)∨(HK s.1 s.2∧P s.1 s.2))) m (Sum.inr u) 3:=by
        dsimp only [markedFiniteDomainBalance]
        simp only [markedFiniteBalance,Matrix.cons_val_succ',Matrix.cons_val_zero'] at hfin ⊢
        convert hfin.symm using 1 <;> congr!
    _ = markedSixDegreeBalance m
      (fun j=>((markedBalanceTermSet (fun a:{e:E//PE e}=>tail a.val) (fun a:{e:E//PE e}=>head a.val)
        (fun a:{e:K//PK e}=>ktail a.val) (fun a:{e:K//PK e}=>khead a.val)
        (fun x u=>H₀ x u∧P x u) (fun x u=>HK x u∧P x u) (Sum.inr u) j).card:ℝ)) 3:=by
        convert hraw using 1 <;> congr!
    _ = _:=by
      apply congrArg (fun d:Fin 6→ℝ=>markedSixDegreeBalance m d 3)
      funext j
      have h:=markedBalanceTermSet_domain_card tail head ktail khead H₀ HK X Z (Sum.inr u) j
      convert congrArg (fun n:ℕ=>(n:ℝ)) h.symm using 1 <;> congr!

end Oberwolfach
