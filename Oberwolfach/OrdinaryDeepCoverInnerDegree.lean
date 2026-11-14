module

public import Oberwolfach.OrdinaryInnerPackingControlledByCorrection
public import Oberwolfach.OrdinaryUnreservedPackingCertificate

@[expose] public section
/-! The exact internal-resource identity of the deep cover bounds the inner
physical degree by the degree of the correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_deep_cover_inner_degree (Q D F:SimpleGraph V) (H J:V→U→Prop)
    (X:Finset V) (Z:Finset U) (r:ℕ)
    (M:Finset (OrdinaryWheel Q F H r)) (E:Finset (Sym2 V⊕(V×U)))
    (hE:M.biUnion ordinaryWheelResources∩ordinaryHostResources (spanningRestriction Q X)
      (fun v u=>H v u∧v∈X∧u∈Z)=E)
    (hEsub:E⊆ordinaryHostResources D J) (δ:ℝ)
    (hD:∀w:V⊕U,((ordinaryPhysicalGraph D J).degree w:ℝ)≤δ):
    ∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M))
      (ordinaryInnerVertices X Z)).degree w:ℝ)≤δ:=by
  have hR:=ordinaryWheelRimGraph_subhost M
  have hS:∀v u,ordinaryPackingSpokes M v u→H v u:=by
    intro v u hvu
    obtain ⟨A,hA,ha,hv⟩:=hvu
    exact ha ▸ A.property.1 v hv
  have hinner:ordinaryHostResources (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M) ∩
      ordinaryHostResources (spanningRestriction Q X) (fun v u=>H v u∧v∈X∧u∈Z)⊆ordinaryHostResources D J:=by
    rw [←ordinaryPacking_resources M,hE]
    exact hEsub
  have hsub:=ordinary_inner_packing_controlled_by_correction Q (ordinaryWheelRimGraph M) D H (ordinaryPackingSpokes M) J X Z hR hS hinner
  intro w
  have hd:((spanningRestriction (ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M))
      (ordinaryInnerVertices X Z)).degree w:ℝ)≤((ordinaryPhysicalGraph D J).degree w:ℝ):=by
    exact_mod_cast SimpleGraph.degree_le_of_le hsub
  exact hd.trans (hD w)
end Oberwolfach
