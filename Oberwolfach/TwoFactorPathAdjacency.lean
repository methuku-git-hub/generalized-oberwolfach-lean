module

public import Oberwolfach.ResidualInternalNeighbors

@[expose] public section
/-! An internal vertex of a simple path in a two-factor is adjacent only to
its immediate predecessor and successor on that path. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem two_factor_path_adjacent_indices (F:SimpleGraph V)
    (hF:F.IsRegularOfDegree 2) {u v:V} (p:F.Walk u v) (hp:p.IsPath)
    (i j:ℕ) (hi0:i≠0) (hilt:i<p.length) (hjle:j≤p.length)
    (hij:F.Adj (p.getVert i) (p.getVert j)):
    j+1=i ∨ i+1=j := by
  have hsub:=p.toSubgraph.neighborSet_subset (p.getVert i)
  have hsmall:(p.toSubgraph.neighborSet (p.getVert i)).ncard=2 :=
    hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hilt
  have hbig:(F.neighborSet (p.getVert i)).ncard=2 := by rw [F.ncard_neighborSet,hF (p.getVert i)]
  have hsets:p.toSubgraph.neighborSet (p.getVert i)=F.neighborSet (p.getVert i) := by
    apply Set.eq_of_subset_of_ncard_le hsub
    rw [hbig,hsmall]
  have hmem:p.getVert j∈p.toSubgraph.neighborSet (p.getVert i) := by rw [hsets];exact hij
  rw [hp.neighborSet_toSubgraph_internal hi0 hilt] at hmem
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hmem
  rcases hmem with h|h
  · left
    have hj:j=i-1 := hp.getVert_injOn (by simpa using hjle) (by simp;omega) h
    omega
  · right
    exact (hp.getVert_injOn (by simp;omega) (by simpa using hjle) h.symm)
end Oberwolfach
