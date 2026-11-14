module

public import Oberwolfach.ResidualIntervalMarkerInterior
public import Oberwolfach.ResidualSelectedRunWalk

@[expose] public section
/-! Marker positions inside a realised selected run are precisely the
strictly internal multiples of the segment length. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem selected_run_marker_interior_iff {F:SimpleGraph V} {u v:V}
    (p:F.Walk u v) (hp:p.IsPath) (c d a b j:ℕ) (hc:0<c)
    (hab:a≤b) (hbd:b<d) (hjd:j≤d) (hlen:p.length=c*d+4):
    p.getVert (2+c*j)∈(selectedRunWalk p c a b hab).support.toFinset \
      {p.getVert (2+c*a),p.getVert (2+c*(b+1))} ↔ a<j ∧ j≤b := by
  have hm:=Nat.mul_le_mul_left c (show b+1≤d by omega)
  have hmj:=Nat.mul_le_mul_left c hjd
  have hr:2+c*(b+1)≤p.length := by rw [hlen];omega
  have hj:2+c*j≤p.length := by rw [hlen];omega
  have hidx:2+c*a≤2+c*(b+1) := by
    have hh:=Nat.mul_le_mul_left c (show a≤b+1 by omega)
    omega
  have hiff:=path_marker_in_interval_interior_iff p hp (2+c*a) (2+c*(b+1)) (2+c*j) hidx hr hj
  change (p.getVert (2+c*j)∈(selectedRunWalk p c a b hab).support.toFinset \
      {p.getVert (2+c*a),p.getVert (2+c*(b+1))}) ↔
      2+c*a<2+c*j ∧ 2+c*j<2+c*(b+1) at hiff
  rw [hiff]
  constructor
  · rintro ⟨h1,h2⟩
    constructor
    · by_contra h
      have hm:=Nat.mul_le_mul_left c (show j≤a by omega)
      omega
    · by_contra h
      have hm:=Nat.mul_le_mul_left c (show b+1≤j by omega)
      omega
  · rintro ⟨h1,h2⟩
    have hm1:=Nat.mul_lt_mul_of_pos_left h1 hc
    have hm2:=Nat.mul_lt_mul_of_pos_left (show j<b+1 by omega) hc
    omega
end Oberwolfach
