module

public import Oberwolfach.TypedMarkedIncidenceIndicators

@[expose] public section
/-! The marked rim resource is indexed by its auxiliary endpoints. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {m b:ℕ} {π:Equiv.Perm V}

theorem marked_closing_arc_iff
    (C:MarkedCycleTuple (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b) (x z:V):
    CanonicalMarkedArcMem C (Sum.inr (x,z)) ↔ C.val (Fin.last m)=x ∧ C.val 0=z := by
  have h:=markedCycleIncidence_canonical_indicator (tail:=Prod.fst) (head:=Prod.snd)
    (ktail:=Prod.fst) (khead:=Prod.snd) (fun _ _ hh=>hh) (fun _ _ hh=>hh) C (Sum.inr (x,z))
  simp only [markedCycleIncidence,Sum.elim_inr,directedEdgeIndicator] at h
  split_ifs at h <;> simp_all [eq_comm]
end Oberwolfach
