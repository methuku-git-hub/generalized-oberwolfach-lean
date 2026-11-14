module

public import Oberwolfach.ResidualCycleSupport
public import Oberwolfach.DisjointActualWalkMatching

@[expose] public section
/-! Removing the first edge of a cycle gives a simple path containing the
entire cycle vertex set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cycle_tail_support_eq
    {X:Type} [Fintype X] [DecidableEq X] (G:SimpleGraph X) {x:X}
    (p:G.Walk x x) (hp:p.IsCycle):p.tail.support.toFinset=p.support.toFinset:=by
  have hperm:=p.support_tail_perm_support_dropLast
  rw [p.support_dropLast hp.not_nil] at hperm
  rw [cycle_walk_support_toFinset G p hp]
  ext z
  simpa only [List.mem_toFinset] using (hperm.mem_iff : z∈p.tail.support ↔ z∈p.support.dropLast)
end Oberwolfach
