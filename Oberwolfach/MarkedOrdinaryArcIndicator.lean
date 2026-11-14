module

public import Oberwolfach.TypedMarkedIncidenceIndicators

@[expose] public section
/-! The ordinary rim indicator counts the nonclosing directed positions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {m b:ℕ} {π:Equiv.Perm V}

theorem marked_ordinary_arc_indicator
    (C:MarkedCycleTuple (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b) (x z:V):
    (if CanonicalMarkedArcMem C (Sum.inl (x,z)) then (1:ℝ) else 0)=
      ∑ i:Fin m,if C.val i.castSucc=x ∧ C.val i.succ=z then 1 else 0 :=by
  have h:=markedCycleIncidence_canonical_indicator (tail:=Prod.fst) (head:=Prod.snd)
    (ktail:=Prod.fst) (khead:=Prod.snd) (fun _ _ hh=>hh) (fun _ _ hh=>hh) C (Sum.inl (x,z))
  simp only [markedCycleIncidence,Sum.elim_inl,directedEdgeIndicator] at h
  calc
    _ = ∑ i:Fin m,if x=C.val i.castSucc ∧ z=C.val i.succ then (1:ℝ) else 0 := h.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have hi : (x=C.val i.castSucc ∧ z=C.val i.succ) ↔
          (C.val i.castSucc=x ∧ C.val i.succ=z) := by
        constructor <;> rintro ⟨a,b⟩ <;> exact ⟨a.symm,b.symm⟩
      split_ifs <;> tauto
end Oberwolfach
