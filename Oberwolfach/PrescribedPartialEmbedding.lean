module

public import Oberwolfach.Definitions

@[expose] public section
/-! An injective partial map is an embedding of its assigned source subtype. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V:Type} [DecidableEq X]

def prescribedPartialEmbedding (A:Finset X) (f:X→V) (hinj:Set.InjOn f A):{x // x∈A}↪V where
  toFun x:=f x.1
  inj' := by
    intro x y h
    apply Subtype.ext
    exact hinj x.2 y.2 h

theorem prescribed_partial_embedding_range (A:Finset X) (f:X→V) (hinj:Set.InjOn f A) (v:V):
    (∃ x,prescribedPartialEmbedding A f hinj x=v) ↔ ∃ x,x∈A ∧ f x=v := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨x.1,x.2,hx⟩
  · rintro ⟨x,hx,hv⟩
    exact ⟨⟨x,hx⟩,hv⟩
end Oberwolfach
