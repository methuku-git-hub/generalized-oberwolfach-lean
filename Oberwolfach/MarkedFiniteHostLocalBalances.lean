module

public import Oberwolfach.MarkedFiniteRemainder
public import Oberwolfach.MarkedMatrixDivisibility

@[expose] public section

/-! The actual retained finite arc and spoke sets, viewed as a typed host.
Local balance is transferred at the specified roots without extending it
to vertices at which the temporary reservation need not be balanced. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

def markedFiniteArcEmbedding (A:Finset (E⊕K)):
    {e:E // Sum.inl e∈A}⊕{e:K // Sum.inr e∈A}↪E⊕K:=
  (Function.Embedding.subtype (fun e:E=>Sum.inl e∈A)).sumMap
    (Function.Embedding.subtype (fun e:K=>Sum.inr e∈A))

theorem markedFiniteArcEmbedding_range (A:Finset (E⊕K)):
    Finset.univ.image (markedFiniteArcEmbedding A)=A:=by
  ext a
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨a',rfl⟩
    cases a' with
    | inl e=>exact e.property
    | inr e=>exact e.property
  · intro ha
    cases a with
    | inl e=>exact ⟨Sum.inl ⟨e,ha⟩,rfl⟩
    | inr e=>exact ⟨Sum.inr ⟨e,ha⟩,rfl⟩

theorem markedFiniteArcEmbedding_filter_card (A:Finset (E⊕K)) (p:E⊕K→Prop):
    (Finset.univ.filter (fun a=>p (markedFiniteArcEmbedding A a))).card=(A.filter p).card:=by
  conv_rhs => rw [←markedFiniteArcEmbedding_range A,Finset.filter_image,
    Finset.card_image_of_injective _ (markedFiniteArcEmbedding A).injective]

theorem marked_finite_host_local_row_balances
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (hS:∀ z∈S,H₀ z.1 z.2∨HK z.1 z.2) (v:V)
    (hd:(A.filter (fun a=>Sum.elim head khead a=v)).card=(A.filter (fun a=>Sum.elim tail ktail a=v)).card)
    (hr:(A.filter (fun a=>Sum.elim head khead a=v)).card=(S.filter (fun z=>z.1=v)).card)
    (hm:(A.filter (fun a=>Sum.elim head khead a=v∧markedArcType a=true)).card=
      (S.filter (fun z=>z.1=v∧HK z.1 z.2)).card):
    let src:=Sum.elim (fun e:{e:E // Sum.inl e∈A}=>tail e.val) (fun e:{e:K // Sum.inr e∈A}=>ktail e.val)
    let dst:=Sum.elim (fun e:{e:E // Sum.inl e∈A}=>head e.val) (fun e:{e:K // Sum.inr e∈A}=>khead e.val)
    let H₀':=fun x u=>H₀ x u∧(x,u)∈S
    let HK':=fun x u=>HK x u∧(x,u)∈S
    (Finset.univ.filter (fun a=>dst a=v)).card=(Finset.univ.filter (fun a=>src a=v)).card∧
    (Finset.univ.filter (fun a=>dst a=v)).card=
      (Finset.univ.filter (fun z:V×U=>(H₀' z.1 z.2∨HK' z.1 z.2)∧z.1=v)).card∧
    (Finset.univ.filter (fun a=>dst a=v∧markedArcType a=true)).card=
      (Finset.univ.filter (fun z:V×U=>HK' z.1 z.2∧z.1=v)).card:=by
  let f:=markedFiniteArcEmbedding A
  have hf (g:E→V) (q:K→V):
      (Finset.univ.filter (fun a=>Sum.elim (fun e:{e:E // Sum.inl e∈A}=>g e.val)
        (fun e:{e:K // Sum.inr e∈A}=>q e.val) a=v)).card=
        (A.filter (fun a=>Sum.elim g q a=v)).card:=by
    convert markedFiniteArcEmbedding_filter_card A (fun a=>Sum.elim g q a=v) using 1
    congr 1
    ext a
    cases a <;> simp [markedFiniteArcEmbedding,markedArcType]
    all_goals congr!
  have hfm:(Finset.univ.filter (fun a=>Sum.elim (fun e:{e:E // Sum.inl e∈A}=>head e.val)
        (fun e:{e:K // Sum.inr e∈A}=>khead e.val) a=v∧markedArcType a=true)).card=
        (A.filter (fun a=>Sum.elim head khead a=v∧markedArcType a=true)).card:=by
    convert markedFiniteArcEmbedding_filter_card A (fun a=>Sum.elim head khead a=v∧markedArcType a=true) using 1
    congr 1
    ext a
    cases a <;> simp [markedFiniteArcEmbedding,markedArcType]
    all_goals congr!
  have hs:(Finset.univ.filter (fun z:V×U=>((H₀ z.1 z.2∧(z.1,z.2)∈S)∨
      (HK z.1 z.2∧(z.1,z.2)∈S))∧z.1=v))=S.filter (fun z=>z.1=v):=by
    ext z
    have hh:=hS z
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Prod.eta]
    tauto
  have hsk:(Finset.univ.filter (fun z:V×U=>(HK z.1 z.2∧(z.1,z.2)∈S)∧z.1=v))=
      S.filter (fun z=>z.1=v∧HK z.1 z.2):=by
    ext z
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Prod.eta]
    tauto
  dsimp only
  rw [hf,hf,hfm,hs,hsk]
  exact ⟨hd,hr,hm⟩

theorem marked_finite_host_local_hub_balance
    (H₀ HK:V→U→Prop) (m:ℕ) (S:Finset (V×U)) (hS:∀ z∈S,H₀ z.1 z.2∨HK z.1 z.2)
    (u:U) (hH:∀ x,¬(H₀ x u∧HK x u))
    (hh:(S.filter (fun z=>z.2=u∧¬HK z.1 z.2)).card=
      m*(S.filter (fun z=>z.2=u∧HK z.1 z.2)).card):
    (Finset.univ.filter (fun x=>H₀ x u∧(x,u)∈S)).card=
      m*(Finset.univ.filter (fun x=>HK x u∧(x,u)∈S)).card:=by
  have hs0:S.filter (fun z=>z.2=u∧¬HK z.1 z.2)=
      Finset.univ.filter (fun z:V×U=>(H₀ z.1 z.2∧(z.1,z.2)∈S)∧z.2=u):=by
    ext z
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Prod.eta]
    constructor
    · rintro ⟨hz,hu,hk⟩
      exact ⟨⟨(hS z hz).resolve_right hk,hz⟩,hu⟩
    · rintro ⟨⟨h0,hz⟩,hu⟩
      refine ⟨hz,hu,?_⟩
      intro hk
      exact hH z.1 (hu ▸ ⟨h0,hk⟩)
  have hsk:S.filter (fun z=>z.2=u∧HK z.1 z.2)=
      Finset.univ.filter (fun z:V×U=>(HK z.1 z.2∧(z.1,z.2)∈S)∧z.2=u):=by
    ext z
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Prod.eta]
    tauto
  have hcol (H:V→U→Prop):
      (Finset.univ.filter (fun z:V×U=>(H z.1 z.2∧(z.1,z.2)∈S)∧z.2=u)).card=
        (Finset.univ.filter (fun x=>H x u∧(x,u)∈S)).card:=by
    convert finite_relation_col_card (fun x y=>H x y∧(x,y)∈S) u using 1 <;> congr!
  rw [hs0,hsk,hcol,hcol] at hh
  exact hh

end Oberwolfach
