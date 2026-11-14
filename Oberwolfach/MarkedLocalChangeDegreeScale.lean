module

public import Oberwolfach.SupportedBernoulliFactor

@[expose] public section
/-! Restricting physical change graphs does not increase degrees; the
ambient loss is converted to the actual active-domain scale. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_local_change_degree_scale
    {V W X Y:Type} [Fintype V] [Fintype W] [Fintype X] [Fintype Y]
    [DecidableEq V] [DecidableEq W] [DecidableEq X] [DecidableEq Y]
    (f:W↪V) (e:X↪Y) (FR:SimpleGraph V) (FS:SimpleGraph Y)
    (iota ζGlobal ζLocal:ℝ)
    (hζLocal:0≤ζLocal) (hsize:iota*Fintype.card V≤(Fintype.card W:ℝ))
    (hsmall:ζGlobal ≤ iota*ζLocal)
    (hFR:∀ v,(FR.degree v:ℝ)≤ζGlobal*Fintype.card V)
    (hFS:∀ y,(FS.degree y:ℝ)≤ζGlobal*Fintype.card V):
    (∀ w,((FR.comap f).degree w:ℝ)≤ζLocal*Fintype.card W) ∧
    (∀ x,((FS.comap e).degree x:ℝ)≤ζLocal*Fintype.card W) := by
  have hn:(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _
  have hglobal:=mul_le_mul_of_nonneg_right hsmall hn
  have hlocal:=mul_le_mul_of_nonneg_left hsize hζLocal
  have hbound:ζGlobal*Fintype.card V≤ζLocal*Fintype.card W:=by nlinarith
  constructor
  · intro w
    exact (Nat.cast_le.mpr (graph_comap_degree_le FR f w)).trans ((hFR (f w)).trans hbound)
  · intro x
    exact (Nat.cast_le.mpr (graph_comap_degree_le FS e x)).trans ((hFS (e x)).trans hbound)
end Oberwolfach
