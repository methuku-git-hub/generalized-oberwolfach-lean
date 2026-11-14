module

public import Oberwolfach.LongProtectedPairEdgeLabels

@[expose] public section
/-! An absorber target contained in a protected list cannot collide with the
already embedded old image. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem protected_list_shields_absorber
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (Lists Old:U→Finset V) (inner:Finset U) (Z:U→Finset V)
    (hOld:∀u,Disjoint (Lists u) (Old u))
    (hZ:∀u,u∈inner→Z u⊆Lists u) (houter:∀u,u∉inner→Z u=∅):
    ∀u,Disjoint (Old u) (Z u):=by
  intro u
  by_cases hu:u∈inner
  · exact (hOld u).symm.mono_right (hZ u hu)
  · rw [houter u hu]
    simp
end Oberwolfach
