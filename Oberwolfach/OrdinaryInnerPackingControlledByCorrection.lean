module

public import Oberwolfach.PhysicalWheelFamilies

@[expose] public section
/-! A packing whose internal resources are contained in a small correction
has physical inner degree at most the degree of that correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_inner_packing_controlled_by_correction
    (Q R D:SimpleGraph V) (H S J:V→U→Prop) (X:Finset V) (Z:Finset U)
    (hR:R≤Q) (hS:∀v u,S v u→H v u)
    (hinner:ordinaryHostResources R S ∩ ordinaryHostResources (spanningRestriction Q X)
      (fun v u=>H v u∧v∈X∧u∈Z) ⊆ ordinaryHostResources D J):
    spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)≤ordinaryPhysicalGraph D J:=by
  intro a b hab
  have hh:=(spanningRestriction_adj _ _ _ _).mp hab
  cases a with
  | inl v=>cases b with
    | inl w=>
      have hv: v∈X:=(ordinaryInnerVertices_left X Z v).mp hh.2.1
      have hw: w∈X:=(ordinaryInnerVertices_left X Z w).mp hh.2.2
      have hres:Sum.inl s(v,w)∈ordinaryHostResources R S:=by rw [ordinaryHostResources_rim];exact hh.1
      have hkeep:Sum.inl s(v,w)∈ordinaryHostResources (spanningRestriction Q X)
          (fun v u=>H v u∧v∈X∧u∈Z):=by
        rw [ordinaryHostResources_rim]
        exact (spanningRestriction_adj Q X v w).mpr ⟨hR hh.1,hv,hw⟩
      have h:=hinner (Finset.mem_inter.mpr ⟨hres,hkeep⟩)
      rw [ordinaryHostResources_rim] at h
      exact h
    | inr u=>
      have hv: v∈X:=(ordinaryInnerVertices_left X Z v).mp hh.2.1
      have hu: u∈Z:=(ordinaryInnerVertices_right X Z u).mp hh.2.2
      have hres:Sum.inr (v,u)∈ordinaryHostResources R S:=(ordinaryHostResources_spoke R S v u).mpr hh.1
      have hkeep:Sum.inr (v,u)∈ordinaryHostResources (spanningRestriction Q X)
          (fun v u=>H v u∧v∈X∧u∈Z):=(ordinaryHostResources_spoke _ _ v u).mpr ⟨hS v u hh.1,hv,hu⟩
      exact (ordinaryHostResources_spoke D J v u).mp (hinner (Finset.mem_inter.mpr ⟨hres,hkeep⟩))
  | inr u=>cases b with
    | inl v=>
      have hu: u∈Z:=(ordinaryInnerVertices_right X Z u).mp hh.2.1
      have hv: v∈X:=(ordinaryInnerVertices_left X Z v).mp hh.2.2
      have hres:Sum.inr (v,u)∈ordinaryHostResources R S:=(ordinaryHostResources_spoke R S v u).mpr hh.1
      have hkeep:Sum.inr (v,u)∈ordinaryHostResources (spanningRestriction Q X)
          (fun v u=>H v u∧v∈X∧u∈Z):=(ordinaryHostResources_spoke _ _ v u).mpr ⟨hS v u hh.1,hv,hu⟩
      exact (ordinaryHostResources_spoke D J v u).mp (hinner (Finset.mem_inter.mpr ⟨hres,hkeep⟩))
    | inr z=>exact hh.1.elim
end Oberwolfach
