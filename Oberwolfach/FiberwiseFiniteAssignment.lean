module

public import Mathlib.Data.Fintype.EquivFin

@[expose] public section
/-! A simultaneous injective assignment respecting a finite label: choose an
injection separately in every fibre and combine these choices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fiberwise_finite_assignment {A B I:Type} [Fintype A] [Fintype B]
    (source:A→I) (target:B→I)
    (h:∀i:I,Fintype.card {a:A // source a=i} ≤ Fintype.card {b:B // target b=i}):
    ∃f:A↪B, ∀a,target (f a)=source a :=by
  classical
  let e : ∀i:I, {a:A // source a=i} ↪ {b:B // target b=i} :=
    fun i => Classical.choice (Function.Embedding.nonempty_of_card_le (h i))
  let f : A → B := fun a => (e (source a) ⟨a,rfl⟩).val
  have hf : Function.Injective f := by
    intro a a' heq
    have hk : source a = source a' := by
      calc
        source a = target (f a) := ((e (source a) ⟨a,rfl⟩).property).symm
        _ = target (f a') := congrArg target heq
        _ = source a' := (e (source a') ⟨a',rfl⟩).property
    have transport : ∀(i j:I) (hij:i=j) (x:A) (hx:source x=j),
        (e i ⟨x,hx.trans hij.symm⟩).val=(e j ⟨x,hx⟩).val := by
      intro i j hij x hx
      subst j
      rfl
    have hr : (e (source a) ⟨a',hk.symm⟩).val = (e (source a') ⟨a',rfl⟩).val :=
      transport _ _ hk a' rfl
    have heq' : (e (source a) ⟨a,rfl⟩).val = (e (source a) ⟨a',hk.symm⟩).val :=
      heq.trans hr.symm
    have he : e (source a) ⟨a,rfl⟩ = e (source a) ⟨a',hk.symm⟩ := Subtype.ext heq'
    exact congrArg Subtype.val ((e (source a)).injective he)
  exact ⟨⟨f,hf⟩,fun a => (e (source a) ⟨a,rfl⟩).property⟩
end Oberwolfach
