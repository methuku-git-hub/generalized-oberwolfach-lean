module

public import Oberwolfach.ResidualRunInteriorsSubset

@[expose] public section
/-! The final-path interior is contained in its two-edge extension. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

def centralPathInterior {F:SimpleGraph V} {u v:V} (p:F.Walk u v) (c d:ℕ):Finset V :=
  (walkInterval p 2 (2+c*d) (by omega)).support.toFinset \ {p.getVert 2,p.getVert (2+c*d)}

theorem central_path_interior_subset {F:SimpleGraph V} {u v:V} (p:F.Walk u v)
    (c d:ℕ) (hlen:p.length=c*d+4):
    centralPathInterior p c d ⊆ p.support.toFinset := by
  intro x hx
  have hx':x∈(walkInterval p 2 (2+c*d) (by omega)).support :=
    List.mem_toFinset.mp (Finset.mem_sdiff.mp hx).1
  have hr:2+c*d≤p.length := by rw [hlen];omega
  obtain ⟨j,_,_,hj⟩:=(walk_interval_mem_support_iff p 2 (2+c*d) (by omega) hr x).mp hx'
  rw [←hj]
  exact List.mem_toFinset.mpr (p.getVert_mem_support j)
end Oberwolfach
