module

public import Oberwolfach.MarkedFiniteInducedLift

@[expose] public section

/-! The correction on the induced pair removes precisely the lifted finite
edge sets from the original induced host. Thus its divisibility identities
hold on the original ambient row and hub types. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_induced_correction_remainder
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (I:Finset V) (J:Finset U) (m:ℕ)
    (DA:Finset ({e:E // tail e∈I∧head e∈I}⊕{e:K // ktail e∈I∧khead e∈I}))
    (DS:Finset (I×J))
    (h:MarkedRemainderDivisible
      (fun e:{e:E // tail e∈I∧head e∈I}=>(⟨tail e.val,e.property.1⟩:I))
      (fun e=>(⟨head e.val,e.property.2⟩:I))
      (fun e:{e:K // ktail e∈I∧khead e∈I}=>(⟨ktail e.val,e.property.1⟩:I))
      (fun e=>(⟨khead e.val,e.property.2⟩:I))
      (fun v:I=>fun u:J=>HK v.val u.val) (Finset.univ\DA)
      ((Finset.univ.filter (fun z:I×J=>H₀ z.1.val z.2.val∨HK z.1.val z.2.val))\DS) m):
    MarkedRemainderDivisible tail head ktail khead HK
      ((Finset.univ.filter (fun a:E⊕K=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I))\
        DA.image (Sum.map Subtype.val Subtype.val))
      ((Finset.univ.filter (fun z:V×U=>H₀ z.1 z.2∨HK z.1 z.2)).filter (fun z=>z.1∈I∧z.2∈J)\
        DS.image (Prod.map Subtype.val Subtype.val)) m:=by
  let f:{e:E // tail e∈I∧head e∈I}⊕{e:K // ktail e∈I∧khead e∈I}→E⊕K:=
    Sum.map Subtype.val Subtype.val
  let g:I×J→V×U:=Prod.map Subtype.val Subtype.val
  have hf:Function.Injective f:=Sum.map_injective.mpr ⟨Subtype.val_injective,Subtype.val_injective⟩
  have hg:Function.Injective g:=by
    intro a b hab
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hab)) (Subtype.ext (congrArg Prod.snd hab))
  have hA:Finset.univ.image f=Finset.univ.filter
      (fun a:E⊕K=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I):=by
    ext a
    simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_filter]
    constructor
    · rintro ⟨a,rfl⟩
      cases a with
      | inl e=>exact e.property
      | inr e=>exact e.property
    · intro ha
      cases a with
      | inl e=>exact ⟨Sum.inl ⟨e,ha⟩,rfl⟩
      | inr e=>exact ⟨Sum.inr ⟨e,ha⟩,rfl⟩
  have hS:(Finset.univ.filter (fun z:I×J=>H₀ z.1.val z.2.val∨HK z.1.val z.2.val)).image g=
      (Finset.univ.filter (fun z:V×U=>H₀ z.1 z.2∨HK z.1 z.2)).filter (fun z=>z.1∈I∧z.2∈J):=by
    ext z
    simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨ha,a.1.property,a.2.property⟩
    · rintro ⟨hz,hI,hJ⟩
      exact ⟨(⟨z.1,hI⟩,⟨z.2,hJ⟩),hz,rfl⟩
  have hl:=marked_induced_finite_divisible_lift tail head ktail khead HK I J m
    (Finset.univ\DA) ((Finset.univ.filter (fun z:I×J=>H₀ z.1.val z.2.val∨HK z.1.val z.2.val))\DS) h
  have ha:(Finset.univ\DA).image f=(Finset.univ.image f)\DA.image f:=Finset.image_sdiff _ _ hf
  have hs:((Finset.univ.filter (fun z:I×J=>H₀ z.1.val z.2.val∨HK z.1.val z.2.val))\DS).image g=
      ((Finset.univ.filter (fun z:I×J=>H₀ z.1.val z.2.val∨HK z.1.val z.2.val)).image g)\DS.image g:=
    Finset.image_sdiff _ _ hg
  rw [hA] at ha
  rw [hS] at hs
  rw [ha,hs] at hl
  exact hl

end Oberwolfach
