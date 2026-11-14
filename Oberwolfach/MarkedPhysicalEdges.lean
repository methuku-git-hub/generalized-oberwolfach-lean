module

public import Oberwolfach.MarkedCycleRepresentation

@[expose] public section

/-! The manuscript's physical map for ordinary and marked arcs. Its supplied
injectivity implies the ordered-endpoint injectivity used by capacity splitting. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def markedPhysicalEdge {V E K : Type*} [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (π : Equiv.Perm V) : E⊕K → Finset V :=
  Sum.elim (fun e => {tail e,head e}) (fun e => {ktail e,π (khead e)})

theorem markedPhysicalEdge_endpoint_injections {V E K : Type*} [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (π : Equiv.Perm V)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π)) :
    Function.Injective (fun e => (tail e,head e)) ∧
      Function.Injective (fun e => (ktail e,khead e)) := by
  constructor
  · intro e f hef
    change (tail e,head e)=(tail f,head f) at hef
    have ht : tail e=tail f := congrArg Prod.fst hef
    have hh : head e=head f := congrArg Prod.snd hef
    apply Sum.inl.inj
    apply hp
    simp only [markedPhysicalEdge,Sum.elim_inl,ht,hh]
  · intro e f hef
    change (ktail e,khead e)=(ktail f,khead f) at hef
    have ht : ktail e=ktail f := congrArg Prod.fst hef
    have hh : khead e=khead f := congrArg Prod.snd hef
    apply Sum.inr.inj
    apply hp
    simp only [markedPhysicalEdge,Sum.elim_inr,ht,hh]

theorem markedCycle_distinct_physical_edges {V E K : Type*} [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (π : Equiv.Perm V) (b : ℕ)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C : MarkedCycleTuple tail head ktail khead m π b) :
    Function.Injective (markedPhysicalEdge tail head ktail khead π ∘
      markedCycleTypedEdge tail head ktail khead m π b C) :=
  markedCycle_physical_images_injective tail head ktail khead m π b C _ hp

end Oberwolfach
