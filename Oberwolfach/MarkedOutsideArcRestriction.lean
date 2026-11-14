module

public import Oberwolfach.MarkedCoverRetainedHost
public import Oberwolfach.MarkedFiniteRemainderTransfer

@[expose] public section

/-! Restrict the actual supplied outside arcs without replacing their
identifiers, endpoints or types. This works for every later finite set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    [DecidableEq E] [DecidableEq K]

theorem marked_outside_arc_restriction
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (X:Finset V)
    (σ:Sym2 (V⊕U)→Bool) (A:Finset (E⊕K))
    (hA:∀ a∈A,Sum.elim tail ktail a∉X∧Sum.elim head khead a∉X):
    let E':={e:E//markedCoverRimAllowed π X σ false (tail e) (head e)}
    let K':={e:K//markedCoverRimAllowed π X σ true (ktail e) (khead e)};
    ∃ f:A→E'⊕K',Function.Injective f∧∀ a,Sum.map Subtype.val Subtype.val (f a)=a.val:=by
  intro E' K'
  have hex (a:A):∃ a':E'⊕K',Sum.map Subtype.val Subtype.val a'=a.val:=by
    cases he:a.val with
    | inl e=>
      have h:=hA a.val a.property
      rw [he] at h
      exact ⟨Sum.inl ⟨e,Or.inl h⟩,rfl⟩
    | inr e=>
      have h:=hA a.val a.property
      rw [he] at h
      exact ⟨Sum.inr ⟨e,Or.inl h⟩,rfl⟩
  choose f hf using hex
  refine ⟨f,?_,hf⟩
  intro a b hab
  apply Subtype.ext
  rw [←hf a,←hf b,hab]
end Oberwolfach
