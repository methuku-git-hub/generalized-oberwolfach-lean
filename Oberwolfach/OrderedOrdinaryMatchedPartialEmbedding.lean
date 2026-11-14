module

public import Oberwolfach.OrderedOrdinaryPhysicalWheel
public import Oberwolfach.OrdinaryAssignedWheelPartialEmbedding

@[expose] public section
/-! The physical matching's unmarked cyclic tuples, once assigned to distinct
components at one hub, define a single partial factor embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordered_ordinary_matched_partial_embedding {n b:ℕ} {A U:Type} [Fintype U] [DecidableEq U]
    (F:SimpleGraph (Fin n)) (hF:F.IsRegularOfDegree 2) (π:Equiv.Perm (Fin n))
    (C:A→F.ConnectedComponent) (hC:Function.Injective C) (len:A→ℕ) (hlen:∀a,3≤len a)
    (W:∀a,OrderedOrdinaryWheel (U:=U) π b (len a)) (u:U)
    (hsize:∀a,Fintype.card (C a)=len a) (hhub:∀a,(W a).2=u)
    (hdis:∀a b,a≠b→Disjoint
      (((orderedOrdinaryResources (W a)).map ordinaryMarkedResourceEmbedding).image (ordinaryMixedPhysicalResource π))
      (((orderedOrdinaryResources (W b)).map ordinaryMarkedResourceEmbedding).image (ordinaryMixedPhysicalResource π))):
    ∃g:∀a,C a↪Fin n,
      (∀a,Set.range (g a)=Set.range (W a).1.val) ∧
      (∀a (x y:C a),(C a).toSimpleGraph.Adj x y↔
        (ordinaryWheelRim (orderedOrdinaryUniversalWheel (hlen a) (W a))).Adj (g a x) (g a y)) ∧
    ∃ψ:{v:Fin n // ∃a,v∈(C a).supp}↪Fin n,
      ∀a (x:C a),ψ ⟨x.val,⟨a,x.property⟩⟩=g a x :=by
  let W':=fun a=>orderedOrdinaryUniversalWheel (hlen a) (W a)
  have hhub':∀a,ordinaryWheelHub (W' a)=u:=by intro a;exact hhub a
  have hdis':∀a b,a≠b→Disjoint (ordinaryWheelResources (W' a)) (ordinaryWheelResources (W' b)):=by
    intro a b hab
    rw [ordered_ordinary_physical_wheel_resources,ordered_ordinary_physical_wheel_resources]
    exact hdis a b hab
  obtain ⟨g,hRange,hGraph,ψ,hψ⟩:=ordinary_assigned_wheels_partial_embedding F hF C hC len W' u hsize hhub' hdis'
  refine ⟨g,?_,hGraph,ψ,hψ⟩
  intro a
  rw [hRange a,ordered_ordinary_universal_support]
end Oberwolfach
