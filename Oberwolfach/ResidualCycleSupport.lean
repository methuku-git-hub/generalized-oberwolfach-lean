module

public import Oberwolfach.ResidualCycleCount

@[expose] public section
/-! A closed simple cycle visits its initial vertex twice but its vertex set
is the finite set of vertices before the final return. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem cycle_walk_support_toFinset (F:SimpleGraph V) {v:V}
    (p:F.Walk v v) (hp:p.IsCycle):
    p.support.toFinset=p.support.dropLast.toFinset := by
  have hlen : p.support.dropLast.length = p.length := by
    simp [List.length_dropLast,p.length_support]
  have hne:p.support.dropLast≠[] := by
    apply List.ne_nil_of_length_pos
    rw [hlen]
    have hh:=hp.isCircuit.three_le_length
    omega
  have hv : v∈p.support.dropLast := by
    have hh:=List.head_mem hne
    simpa [List.head_dropLast,p.head_support] using hh
  have hclosed:p.support.dropLast++[v]=p.support := by
    simpa using List.dropLast_append_getLast p.support_ne_nil
  ext x
  simp only [List.mem_toFinset]
  have hmem : (x∈p.support.dropLast ∨ x=v) ↔ x∈p.support := by
    simpa only [List.mem_append,List.mem_singleton] using
      Iff.of_eq (congrArg (fun xs : List V => x∈xs) hclosed)
  constructor
  · intro hx
    rcases hmem.2 hx with h|rfl
    · exact h
    · exact hv
  · intro hx
    exact hmem.1 (Or.inl hx)

theorem cycle_walk_edge_full_vertex_count (F:SimpleGraph V) {v:V}
    (p:F.Walk v v) (hp:p.IsCycle):
    p.edges.toFinset.card=p.support.toFinset.card := by
  rw [cycle_walk_support_toFinset F p hp]
  exact cycle_walk_edge_vertex_count F p hp
end Oberwolfach
