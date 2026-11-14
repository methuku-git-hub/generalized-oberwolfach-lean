module

public import Oberwolfach.ResidualSelectedRunWalkDisjoint

@[expose] public section
/-! Distinct marker indices on an extended simple path name distinct vertices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem extended_path_marker_injOn {F:SimpleGraph V} {u v:V} (p:F.Walk u v)
    (hp:p.IsPath) (c d:ℕ) (hc:0<c) (hlen:p.length=c*d+4):
    Set.InjOn (fun j:ℕ=>p.getVert (2+c*j)) (Finset.range (d+1):Finset ℕ) := by
  intro a ha b hb heq
  have had:a≤d := by simpa using ha
  have hbd:b≤d := by simpa using hb
  have hia:2+c*a≤p.length := by
    have hh:=Nat.mul_le_mul_left c had
    rw [hlen];omega
  have hib:2+c*b≤p.length := by
    have hh:=Nat.mul_le_mul_left c hbd
    rw [hlen];omega
  have hidx:=hp.getVert_injOn (by simpa using hia) (by simpa using hib) heq
  have hm:c*a=c*b := by omega
  exact Nat.eq_of_mul_eq_mul_left hc hm

theorem extended_path_marker_image_card {F:SimpleGraph V} {u v:V} (p:F.Walk u v)
    (hp:p.IsPath) (c d:ℕ) (hc:0<c) (hlen:p.length=c*d+4)
    (T:Finset ℕ) (hT:T⊆Finset.range (d+1)):
    (T.image (fun j=>p.getVert (2+c*j))).card=T.card := by
  apply Finset.card_image_iff.mpr
  exact (extended_path_marker_injOn p hp c d hc hlen).mono hT
end Oberwolfach
