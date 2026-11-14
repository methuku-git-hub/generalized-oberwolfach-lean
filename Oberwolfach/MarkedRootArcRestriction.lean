module

public import Oberwolfach.MarkedWheelRestriction
public import Oberwolfach.GraphSelectionDegrees
public import Mathlib.Logic.Embedding.Set
public import Mathlib.Logic.Equiv.Sum

@[expose] public section

/-! Restrict actual root arc indices after deleting physical edges wholly
inside an invariant free set. Auxiliary heads and physical heads are kept
separate, in particular for incoming marked arcs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E T Z : Type} [DecidableEq V]

 def restrictedSumEmbedding (f : Z ↪ E⊕T) (PE : E→Prop) (PT : T→Prop)
    (h : ∀ z,Sum.elim PE PT (f z)) : Z ↪ {e // PE e}⊕{t // PT t} :=
  (Function.Embedding.codRestrict (fun a=>Sum.elim PE PT a) f h).trans
    Equiv.subtypeSum.toEmbedding

theorem restrictedSumEmbedding_forget (f : Z ↪ E⊕T) (PE : E→Prop) (PT : T→Prop)
    (h : ∀ z,Sum.elim PE PT (f z)) (z : Z) :
    Sum.map Subtype.val Subtype.val (restrictedSumEmbedding f PE PT h z)=f z := by
  cases he : f z <;> simp [restrictedSumEmbedding,Function.Embedding.codRestrict,Equiv.subtypeSum,he]

theorem restrictedSumEmbedding_elim {W : Type} (f : Z ↪ E⊕T) (PE : E→Prop) (PT : T→Prop)
    (h : ∀ z,Sum.elim PE PT (f z)) (g : E→W) (k : T→W) (z : Z) :
    Sum.elim (fun e=>g e.val) (fun t=>k t.val) (restrictedSumEmbedding f PE PT h z)=
      Sum.elim g k (f z) := by
  rw [←restrictedSumEmbedding_forget f PE PT h z]
  cases restrictedSumEmbedding f PE PT h z <;> rfl

theorem restrictedSumEmbedding_type (f : Z ↪ E⊕T) (PE : E→Prop) (PT : T→Prop)
    (h : ∀ z,Sum.elim PE PT (f z)) (z : Z) :
    (restrictedSumEmbedding f PE PT h z).isRight=(f z).isRight := by
  rw [←restrictedSumEmbedding_forget f PE PT h z]
  cases restrictedSumEmbedding f PE PT h z <;> rfl

theorem marked_root_arc_survives_free_deletion
    (tail head : E→V) (ktail khead : T→V) (π : Equiv.Perm V)
    (F : Finset V) (hF : ∀ z,π z∈F ↔ z∈F) (D : SimpleGraph V)
    (hD : GraphSupportedOn F D) (v : V) (hv : v∉F) (a : E⊕T)
    (ha : Sum.elim tail ktail a=v ∨ Sum.elim head khead a=v) :
    Sum.elim (fun e=>¬D.Adj (tail e) (head e))
      (fun e=>¬D.Adj (ktail e) (π (khead e))) a := by
  cases a with
  | inl e=>
    intro he
    rcases ha with ha|ha
    · exact hv (ha ▸ (hD _ _ he).1)
    · exact hv (ha ▸ (hD _ _ he).2)
  | inr t=>
    intro ht
    rcases ha with ha|ha
    · exact hv (ha ▸ (hD _ _ ht).1)
    · exact hv (ha ▸ (hF _).mp (hD _ _ ht).2)

end Oberwolfach
