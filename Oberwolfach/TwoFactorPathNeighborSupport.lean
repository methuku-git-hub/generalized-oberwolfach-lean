module

public import Oberwolfach.TwoFactorPathAdjacency

@[expose] public section
/-! All neighbours of an internal path vertex remain on the path. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem two_factor_internal_neighbors_on_path (F:SimpleGraph V)
    (hF:F.IsRegularOfDegree 2) {u v:V} (p:F.Walk u v) (hp:p.IsPath)
    (i:ℕ) (hi0:i≠0) (hilt:i<p.length) (y:V)
    (hxy:F.Adj (p.getVert i) y): y∈p.support.toFinset := by
  have hint:p.getVert i∈p.support.toFinset \ {u,v} := by
    apply Finset.mem_sdiff.mpr
    constructor
    · apply List.mem_toFinset.mpr
      exact p.getVert_mem_support i
    · simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
      constructor
      · intro h
        exact hi0 ((hp.getVert_eq_start_iff (Nat.le_of_lt hilt)).mp h)
      · intro h
        have hh: i=p.length := (hp.getVert_eq_end_iff (Nat.le_of_lt hilt)).mp h
        omega
  have he:=two_factor_internal_path_edges F hF p hp (p.getVert i) y hint hxy
  exact List.mem_toFinset.mpr (p.snd_mem_support_of_mem_edges (List.mem_toFinset.mp he))
end Oberwolfach
