module

public import Oberwolfach.PhysicalWheelFamilies

@[expose] public section
/-! Typed rim/spoke resource disjointness is equivalent to physical graph
edge-disjointness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_host_resource_disjoint_iff_physical (Q R:SimpleGraph V) (H K:V→U→Prop):
    Disjoint (ordinaryHostResources Q H) (ordinaryHostResources R K) ↔
      Disjoint (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph R K) := by
  constructor
  · intro h
    apply disjoint_iff_inf_le.mpr
    intro x y hxy
    cases x with
    | inl v=>cases y with
      | inl w=>
        apply (Finset.disjoint_left.mp h) (a:=Sum.inl s(v,w))
        · rw [ordinaryHostResources_rim];exact hxy.1
        · rw [ordinaryHostResources_rim];exact hxy.2
      | inr u=>
        apply (Finset.disjoint_left.mp h) (a:=Sum.inr (v,u))
        · rw [ordinaryHostResources_spoke];exact hxy.1
        · rw [ordinaryHostResources_spoke];exact hxy.2
    | inr u=>cases y with
      | inl v=>
        apply (Finset.disjoint_left.mp h) (a:=Sum.inr (v,u))
        · rw [ordinaryHostResources_spoke];exact hxy.1
        · rw [ordinaryHostResources_spoke];exact hxy.2
      | inr z=>exact hxy.1
  · intro h
    apply Finset.disjoint_left.mpr
    intro e he hf
    cases e with
    | inl e=>
      rw [ordinaryHostResources_rim] at he hf
      induction e using Sym2.ind with
      | _ v w=>
        exact (disjoint_iff_inf_le.mp h) (v:=Sum.inl v) (w:=Sum.inl w) ⟨he,hf⟩
    | inr vu=>
      rcases vu with ⟨v,u⟩
      rw [ordinaryHostResources_spoke] at he hf
      exact (disjoint_iff_inf_le.mp h) (v:=Sum.inl v) (w:=Sum.inr u) ⟨he,hf⟩
end Oberwolfach
