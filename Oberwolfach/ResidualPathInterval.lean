module

public import Oberwolfach.ResidualRunInternalCounts
public import Oberwolfach.FactorComponentOrderedCycle

@[expose] public section
/-! An interval of an actual graph walk, with its exact endpoints. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

def walkInterval {F:SimpleGraph V} {u v:V} (p:F.Walk u v)
    (a b:ℕ) (hab:a≤b):F.Walk (p.getVert a) (p.getVert b) :=
  ((p.drop a).take (b-a)).copy rfl (by simp [Nat.add_sub_of_le hab])

theorem walk_interval_length {F:SimpleGraph V} {u v:V} (p:F.Walk u v)
    (a b:ℕ) (hab:a≤b) (hb:b≤p.length):
    (walkInterval p a b hab).length=b-a := by
  simp only [walkInterval,SimpleGraph.Walk.length_copy,SimpleGraph.Walk.take_length,
    SimpleGraph.Walk.drop_length]
  apply Nat.min_eq_left
  omega

theorem walk_interval_isPath {F:SimpleGraph V} {u v:V} (p:F.Walk u v)
    (hp:p.IsPath) (a b:ℕ) (hab:a≤b):
    (walkInterval p a b hab).IsPath := by
  simpa [walkInterval] using (hp.drop a).take (b-a)

theorem walk_interval_getVert {F:SimpleGraph V} {u v:V} (p:F.Walk u v)
    (a b:ℕ) (hab:a≤b) (k:ℕ) (hk:k≤b-a):
    (walkInterval p a b hab).getVert k=p.getVert (a+k) := by
  simp [walkInterval,Nat.min_eq_right hk]
end Oberwolfach
