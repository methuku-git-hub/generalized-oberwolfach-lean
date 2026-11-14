module

public import Oberwolfach.MarkedFiniteRemainder

@[expose] public section

/-! Four exact divisibility identities under restriction of typed rim
identifiers. Spoke types are compared on the actual finite spoke set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
  {tail head:E→V} {ktail khead:K→V} {HK:V→U→Prop} {m:ℕ}

theorem marked_remainder_divisible_subhost_iff
    (PE:E→Prop) (PK:K→Prop) (PS:V×U→Prop)
    (A:Finset ({e // PE e}⊕{e // PK e})) (S:Finset (V×U)) (hS:∀ s∈S,PS s):
    MarkedRemainderDivisible (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val)
      (fun v u=>HK v u∧PS (v,u)) A S m ↔
    MarkedRemainderDivisible tail head ktail khead HK
      (A.image (Sum.map Subtype.val Subtype.val)) S m:=by
  let f:{e // PE e}⊕{e // PK e}→E⊕K:=Sum.map Subtype.val Subtype.val
  have hf:Function.Injective f:=Sum.map_injective.mpr ⟨Subtype.val_injective,Subtype.val_injective⟩
  have hsrc (a:{e // PE e}⊕{e // PK e}):Sum.elim tail ktail (f a)=
      Sum.elim (fun e:{e // PE e}=>tail e.val) (fun e:{e // PK e}=>ktail e.val) a:=by cases a <;> rfl
  have hdst (a:{e // PE e}⊕{e // PK e}):Sum.elim head khead (f a)=
      Sum.elim (fun e:{e // PE e}=>head e.val) (fun e:{e // PK e}=>khead e.val) a:=by cases a <;> rfl
  have htype (a:{e // PE e}⊕{e // PK e}):markedArcType (f a)=markedArcType a:=by cases a <;> rfl
  have hcount (p:E⊕K→Prop):((A.image f).filter p).card=(A.filter (fun a=>p (f a))).card:=by
    rw [Finset.filter_image,Finset.card_image_of_injective _ hf]
  have hmarked (v:V):S.filter (fun s=>s.1=v∧HK s.1 s.2∧PS (s.1,s.2))=
      S.filter (fun s=>s.1=v∧HK s.1 s.2):=by
    ext s
    simp only [Finset.mem_filter]
    constructor
    · tauto
    · rintro ⟨hs,hv,hk⟩
      exact ⟨hs,hv,hk,hS s hs⟩
  have hhub (u:U):S.filter (fun s=>s.2=u∧HK s.1 s.2∧PS (s.1,s.2))=
      S.filter (fun s=>s.2=u∧HK s.1 s.2):=by
    ext s
    simp only [Finset.mem_filter]
    constructor
    · tauto
    · rintro ⟨hs,hv,hk⟩
      exact ⟨hs,hv,hk,hS s hs⟩
  have hhub0 (u:U):S.filter (fun s=>s.2=u∧¬(HK s.1 s.2∧PS (s.1,s.2)))=
      S.filter (fun s=>s.2=u∧¬HK s.1 s.2):=by
    ext s
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hs,hu,hn⟩
      exact ⟨hs,hu,fun hk=>hn ⟨hk,hS s hs⟩⟩
    · tauto
  have hd (v:V):((A.image f).filter (fun a=>Sum.elim head khead a=v)).card=
      (A.filter (fun a=>Sum.elim (fun e:{e // PE e}=>head e.val) (fun e:{e // PK e}=>khead e.val) a=v)).card:=by
    convert hcount (fun a=>Sum.elim head khead a=v) using 1 <;> congr! <;> simp only [hdst]
  have ht (v:V):((A.image f).filter (fun a=>Sum.elim tail ktail a=v)).card=
      (A.filter (fun a=>Sum.elim (fun e:{e // PE e}=>tail e.val) (fun e:{e // PK e}=>ktail e.val) a=v)).card:=by
    convert hcount (fun a=>Sum.elim tail ktail a=v) using 1 <;> congr! <;> simp only [hsrc]
  have hm (v:V):((A.image f).filter (fun a=>Sum.elim head khead a=v∧markedArcType a=true)).card=
      (A.filter (fun a=>Sum.elim (fun e:{e // PE e}=>head e.val) (fun e:{e // PK e}=>khead e.val) a=v∧markedArcType a=true)).card:=by
    convert hcount (fun a=>Sum.elim head khead a=v∧markedArcType a=true) using 1 <;> congr! <;> simp only [hdst,htype]
  constructor
  · intro h
    constructor
    · intro v
      exact (hd v).trans ((h.directed v).trans (ht v).symm)
    · intro v
      exact (hd v).trans (h.row v)
    · intro v
      have hh:(A.filter (fun a=>Sum.elim (fun e:{e // PE e}=>head e.val) (fun e:{e // PK e}=>khead e.val) a=v∧markedArcType a=true)).card=
        (S.filter (fun s=>s.1=v∧HK s.1 s.2∧PS (s.1,s.2))).card:=by
        convert h.marked v using 1 <;> congr!
      rw [hmarked] at hh
      exact (hm v).trans hh
    · intro u
      have hh:(S.filter (fun s=>s.2=u∧¬(HK s.1 s.2∧PS (s.1,s.2)))).card=
        m*(S.filter (fun s=>s.2=u∧HK s.1 s.2∧PS (s.1,s.2))).card:=by
        convert h.hub u using 1 <;> congr!
      rw [hhub0,hhub] at hh
      exact hh
  · intro h
    constructor
    · intro v
      exact (hd v).symm.trans ((h.directed v).trans (ht v))
    · intro v
      exact (hd v).symm.trans (h.row v)
    · intro v
      have hh:(A.filter (fun a=>Sum.elim (fun e:{e // PE e}=>head e.val) (fun e:{e // PK e}=>khead e.val) a=v∧markedArcType a=true)).card=
        (S.filter (fun s=>s.1=v∧HK s.1 s.2∧PS (s.1,s.2))).card:=by
        rw [hmarked]
        exact (hm v).symm.trans (h.marked v)
      convert hh using 1 <;> congr!
    · intro u
      have hh:(S.filter (fun s=>s.2=u∧¬(HK s.1 s.2∧PS (s.1,s.2)))).card=
        m*(S.filter (fun s=>s.2=u∧HK s.1 s.2∧PS (s.1,s.2))).card:=by
        rw [hhub0,hhub]
        exact h.hub u
      convert hh using 1 <;> congr!

theorem marked_remainder_restrict_arcs [Fintype E] [Fintype K]
    (PE:E→Prop) (PK:K→Prop) (A:Finset (E⊕K)) (hA:∀ a∈A,Sum.elim PE PK a):
    ∃ A':Finset ({e // PE e}⊕{e // PK e}),
      A'.image (Sum.map Subtype.val Subtype.val)=A:=by
  refine ⟨Finset.univ.filter (fun a=>Sum.map Subtype.val Subtype.val a∈A),?_⟩
  ext a
  constructor
  · rintro ha
    obtain ⟨a',ha',rfl⟩:=Finset.mem_image.mp ha
    exact (Finset.mem_filter.mp ha').2
  · intro ha
    cases a with
    | inl e=>exact Finset.mem_image.mpr ⟨Sum.inl ⟨e,hA _ ha⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩,rfl⟩
    | inr e=>exact Finset.mem_image.mpr ⟨Sum.inr ⟨e,hA _ ha⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩,rfl⟩

end Oberwolfach
