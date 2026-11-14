module

public import Oberwolfach.MarkedBalanceTestSets
public import Oberwolfach.MarkedPackingTransport

@[expose] public section

/-! Restricting the two rim types and both spoke types preserves the six
fixed test sets exactly under the original occurrence embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop}

theorem markedBalanceTerm_toLarger (PE:E→Prop) (PK:K→Prop) (P:V→U→Prop)
    (r:V⊕U) (j:Fin 6)
    (a:MarkedActiveEdge {e//PE e} {e//PK e} (fun x u=>H₀ x u∧P x u) (fun x u=>HK x u∧P x u)):
    markedBalanceTerm (fun e:{e//PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e//PK e}=>ktail e.val) (fun e=>khead e.val)
      (fun x u=>H₀ x u∧P x u) (fun x u=>HK x u∧P x u) r j a↔
    markedBalanceTerm tail head ktail khead H₀ HK r j
      (markedActiveToLarger PE PK (fun (x:V) (u:U) (h:H₀ x u∧P x u)=>h.1) (fun (x:V) (u:U) (h:HK x u∧P x u)=>h.1) a):=by
  rcases a with (a|a)|a
  · cases r <;> rfl
  · cases r <;> rfl
  · have hp:P a.val.1 a.val.2:=a.property.elim And.right And.right
    cases r <;> simp only [markedBalanceTerm,markedActiveToLarger,Sum.map_inr,
      Sum.elim_inr,hp,and_true]

theorem markedBalanceTermSet_restriction_card (PE:E→Prop) (PK:K→Prop) (P:V→U→Prop)
    (r:V⊕U) (j:Fin 6):
    (markedBalanceTermSet (fun e:{e//PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e//PK e}=>ktail e.val) (fun e=>khead e.val)
      (fun x u=>H₀ x u∧P x u) (fun x u=>HK x u∧P x u) r j).card=
    ((markedBalanceTermSet tail head ktail khead H₀ HK r j).filter
      (markedActiveRetained PE PK (fun x u=>H₀ x u∧P x u) (fun x u=>HK x u∧P x u))).card:=by
  classical
  let f:=markedActiveToLarger PE PK (fun (x:V) (u:U) (h:H₀ x u∧P x u)=>h.1) (fun (x:V) (u:U) (h:HK x u∧P x u)=>h.1)
  let S:=markedBalanceTermSet (fun e:{e//PE e}=>tail e.val) (fun e=>head e.val)
    (fun e:{e//PK e}=>ktail e.val) (fun e=>khead e.val)
    (fun x u=>H₀ x u∧P x u) (fun x u=>HK x u∧P x u) r j
  have he:S.image f=(markedBalanceTermSet tail head ktail khead H₀ HK r j).filter
      (markedActiveRetained PE PK (fun x u=>H₀ x u∧P x u) (fun x u=>HK x u∧P x u)):=by
    ext a
    constructor
    · intro ha
      obtain ⟨a',ha',rfl⟩:=Finset.mem_image.mp ha
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
      · exact (markedBalanceTerm_toLarger PE PK P r j a').mp (Finset.mem_filter.mp ha').2
      · exact (markedActiveToLarger_range PE PK _ _ _).mp ⟨a',rfl⟩
    · intro ha
      obtain ⟨ha,hkeep⟩:=Finset.mem_filter.mp ha
      obtain ⟨a',he'⟩:=(markedActiveToLarger_range PE PK
        (fun (x:V) (u:U) (h:H₀ x u∧P x u)=>h.1) (fun (x:V) (u:U) (h:HK x u∧P x u)=>h.1) a).mpr hkeep
      refine Finset.mem_image.mpr ⟨a',?_,he'⟩
      simp only [S,markedBalanceTermSet,Finset.mem_filter,Finset.mem_univ,true_and]
      apply (markedBalanceTerm_toLarger PE PK P r j a').mpr
      rw [he']
      exact (Finset.mem_filter.mp ha).2
  have hc:=congrArg Finset.card he
  rw [Finset.card_image_of_injective _ (markedActiveToLarger_injective PE PK _ _)] at hc
  exact hc
end Oberwolfach
