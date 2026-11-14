module

public import Oberwolfach.MarkedFiniteRemainder

@[expose] public section

/-! The active row and hub sets of a remainder are its actual incident
vertices. Isolated ambient vertices do not enter the input-size bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

def markedRemainderRows (tail head:E→V) (ktail khead:K→V) (A:Finset (E⊕K)) (S:Finset (V×U)):
    Finset V:=A.image (Sum.elim tail ktail)∪A.image (Sum.elim head khead)∪S.image Prod.fst

def markedRemainderHubs (S:Finset (V×U)):Finset U:=S.image Prod.snd

theorem markedRemainderGraph_active_rows (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A:Finset (E⊕K)) (S:Finset (V×U)):
    (markedRemainderGraph tail head ktail khead HK A S).activeRows=markedRemainderRows tail head ktail khead A S:=by
  ext v
  simp [IndexedMarkedGraph.activeRows,markedRemainderRows,markedRemainderGraph]

theorem markedRemainderGraph_active_hubs (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A:Finset (E⊕K)) (S:Finset (V×U)):
    (markedRemainderGraph tail head ktail khead HK A S).activeHubs=markedRemainderHubs S:=by
  ext u
  simp [IndexedMarkedGraph.activeHubs,markedRemainderHubs,markedRemainderGraph]

theorem markedRemainderRealization_active_sets
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V) (b:ℕ)
    (A:Finset (E⊕K)) (S:Finset (V×U))
    (hS:∀ s∈S,H₀ s.1 s.2∨HK s.1 s.2)
    (hsep:∀ a∈A,¬PermutationClose π b (Sum.elim tail ktail a) (Sum.elim head khead a))
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)):
    let R:=markedRemainderRealization tail head ktail khead H₀ HK π b A S hS hsep hp
    R.active.rowSet=markedRemainderRows tail head ktail khead A S∧R.active.hubSet=markedRemainderHubs S:=by
  intro R
  have hr:R.active.rowSet=(markedRemainderGraph tail head ktail khead HK A S).activeRows:=by
    ext v
    change v∈Finset.univ.image (fun x:(markedRemainderGraph tail head ktail khead HK A S).activeRows=>x.val)↔_
    simp
  have hh:R.active.hubSet=(markedRemainderGraph tail head ktail khead HK A S).activeHubs:=by
    ext u
    change u∈Finset.univ.image (fun x:(markedRemainderGraph tail head ktail khead HK A S).activeHubs=>x.val)↔_
    simp
  exact ⟨hr.trans (markedRemainderGraph_active_rows _ _ _ _ _ _ _),
    hh.trans (markedRemainderGraph_active_hubs _ _ _ _ _ _ _)⟩

end Oberwolfach
