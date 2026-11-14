module

public import Oberwolfach.MarkedFiniteVertexEmbedding
public import Oberwolfach.MarkedRemainderSubhost

@[expose] public section

/-! Lift a divisible finite remainder on an induced row/hub pair to the
original host. Every original edge occurrence and both spoke types are
preserved; vertices outside the pair have zero incidence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  [DecidableEq E] [DecidableEq K]

theorem marked_induced_finite_divisible_lift
    (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop) (I:Finset V) (J:Finset U) (m:ℕ)
    (A:Finset ({e:E // tail e∈I∧head e∈I}⊕{e:K // ktail e∈I∧khead e∈I}))
    (S:Finset (I×J))
    (h:MarkedRemainderDivisible
      (fun e:{e:E // tail e∈I∧head e∈I}=>(⟨tail e.val,e.property.1⟩:I))
      (fun e=>(⟨head e.val,e.property.2⟩:I))
      (fun e:{e:K // ktail e∈I∧khead e∈I}=>(⟨ktail e.val,e.property.1⟩:I))
      (fun e=>(⟨khead e.val,e.property.2⟩:I))
      (fun v:I=>fun u:J=>HK v.val u.val) A S m):
    MarkedRemainderDivisible tail head ktail khead HK
      (A.image (Sum.map Subtype.val Subtype.val)) (S.image (Prod.map Subtype.val Subtype.val)) m:=by
  let f:I↪V:=⟨Subtype.val,Subtype.val_injective⟩
  let g:J↪U:=⟨Subtype.val,Subtype.val_injective⟩
  have hh:=marked_finite_remainder_vertex_image_divisible
    (fun e:{e:E // tail e∈I∧head e∈I}=>(⟨tail e.val,e.property.1⟩:I))
    (fun e=>(⟨head e.val,e.property.2⟩:I))
    (fun e:{e:K // ktail e∈I∧khead e∈I}=>(⟨ktail e.val,e.property.1⟩:I))
    (fun e=>(⟨khead e.val,e.property.2⟩:I))
    (fun v:I=>fun u:J=>HK v.val u.val) HK f g A S m (fun _ _=>Iff.rfl) h
  have hh':MarkedRemainderDivisible
      (fun e:{e:E // tail e∈I∧head e∈I}=>tail e.val) (fun e=>head e.val)
      (fun e:{e:K // ktail e∈I∧khead e∈I}=>ktail e.val) (fun e=>khead e.val)
      (fun v u=>HK v u∧True) A (S.image (Prod.map Subtype.val Subtype.val)) m:=by
    simp only [f,g,Function.Embedding.coeFn_mk,Function.comp_def] at hh
    simp only [and_true]
    convert hh using 1 <;> congr!
  exact (marked_remainder_divisible_subhost_iff
    (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (HK:=HK)
    (fun e=>tail e∈I∧head e∈I) (fun e=>ktail e∈I∧khead e∈I) (fun _=>True)
    A (S.image (Prod.map Subtype.val Subtype.val)) (fun _ _=>trivial)).mp hh'

end Oberwolfach
