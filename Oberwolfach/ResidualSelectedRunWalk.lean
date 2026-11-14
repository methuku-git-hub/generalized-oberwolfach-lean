module

public import Oberwolfach.ResidualPathIntervalSupport
public import Oberwolfach.ResidualRunsSeparated

@[expose] public section
/-! Realise a maximal selected run as an actual simple subpath of its
extended path, preserving its endpoints and length. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

def selectedRunWalk {F:SimpleGraph V} {u v:V} (p:F.Walk u v)
    (c a b:ℕ) (hab:a≤b):
    F.Walk (p.getVert (2+c*a)) (p.getVert (2+c*(b+1))) :=
  walkInterval p (2+c*a) (2+c*(b+1)) (by
    have hh:=Nat.mul_le_mul_left c (show a≤b+1 by omega)
    omega)

theorem selected_run_walk_properties {F:SimpleGraph V} {u v:V} (p:F.Walk u v)
    (hp:p.IsPath) (c d a b:ℕ) (hc:0<c) (hab:a≤b) (hb:b<d)
    (hlen:p.length=c*d+4):
    (selectedRunWalk p c a b hab).IsPath ∧
    (selectedRunWalk p c a b hab).length=c*(b+1-a) ∧
    p.getVert (2+c*a)≠p.getVert (2+c*(b+1)) ∧
    ∀ x,x∈(selectedRunWalk p c a b hab).support ↔
      ∃ j,2+c*a≤j ∧ j≤2+c*(b+1) ∧ p.getVert j=x := by
  have hm:=Nat.mul_le_mul_left c (show b+1≤d by omega)
  have hright:2+c*(b+1)≤p.length := by rw [hlen];omega
  have hleft:2+c*a<2+c*(b+1) := by
    have hh:=Nat.mul_lt_mul_of_pos_left (show a<b+1 by omega) hc
    omega
  have hidx:2+c*a≤2+c*(b+1) := by omega
  refine ⟨walk_interval_isPath p hp _ _ hidx,?_,
    path_interval_endpoints_ne p hp _ _ hleft hright,?_⟩
  · have hh:=walk_interval_length p _ _ hidx hright
    change (selectedRunWalk p c a b hab).length=(2+c*(b+1))-(2+c*a) at hh
    rw [hh,Nat.add_sub_add_left,←Nat.mul_sub_left_distrib]
  · intro x
    exact walk_interval_mem_support_iff p _ _ hidx hright x
end Oberwolfach
