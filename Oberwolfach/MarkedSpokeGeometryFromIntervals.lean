module

public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section
/-! Marked spoke geometry follows when ordinary spokes avoid the marked
vertices and their successors at each hub. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_spoke_geometry_from_marked_sets
    {V U:Type} [Fintype V] [DecidableEq V] [DecidableEq U]
    (π:Equiv.Perm V) (Y:U→Finset V) (H:Bool→V→U→Prop)
    (hmarked:∀ v u,H true v u↔v∈Y u)
    (hordinary:∀ v u,H false v u→v∉Y u ∧ v∉(Y u).image π):
    (∀ u v,¬(H false v u∧H true v u)) ∧
    (∀ u v z,H false v u→H true z u→v≠π z) := by
  constructor
  · intro u v h
    exact (hordinary v u h.1).1 ((hmarked v u).mp h.2)
  · intro u v z h0 hK hv
    have hz:z∈Y u:=(hmarked z u).mp hK
    apply (hordinary v u h0).2
    rw [hv]
    exact Finset.mem_image.mpr ⟨z,hz,rfl⟩

theorem marked_spoke_geometry_restrict
    {V U W Z:Type} (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (f:W↪V) (g:Z→U) (hcomm:∀ x,f (ρ x)=π (f x)) (H:Bool→V→U→Prop)
    (htypes:∀ u v,¬(H false v u∧H true v u))
    (hsep:∀ u v z,H false v u→H true z u→v≠π z):
    (∀ u v,¬(H false (f v) (g u)∧H true (f v) (g u))) ∧
    (∀ u v z,H false (f v) (g u)→H true (f z) (g u)→v≠ρ z) := by
  constructor
  · intro u v
    exact htypes (g u) (f v)
  · intro u v z h0 hK heq
    apply hsep (g u) (f v) (f z) h0 hK
    rw [heq,hcomm]
end Oberwolfach
