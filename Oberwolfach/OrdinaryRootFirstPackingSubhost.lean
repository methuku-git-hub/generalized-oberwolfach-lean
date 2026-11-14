module

public import Oberwolfach.OrdinaryRootFirstPackingContext
public import Oberwolfach.OrdinaryPackingPhysicalSubhost
public import Oberwolfach.OrdinaryPhysicalPairMap

@[expose] public section
/-! The selected root-free packing uses only the actual ambient unreserved
physical edges, and hence avoids the inner pair and the reserve. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_packing_subhost
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t:ℝ)
    (K:OrdinaryRootFirstPackingContext Q F H X T Z W r η ell t):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    let φ:A↪V:=⟨Subtype.val,Subtype.val_injective⟩;
    let ψ:B↪U:=⟨Subtype.val,Subtype.val_injective⟩;
    let Q':=Q\K.cover.rim;let H':=fun v u=>H v u∧¬K.cover.spokes v u;
    let D:=(ordinaryWheelRimGraph K.packing.wheels).map φ;
    let E:=ordinaryMappedSpokes (ordinaryPackingSpokes K.packing.wheels) φ ψ;
    ordinaryPhysicalGraph D E≤ordinaryPhysicalGraph (ordinaryUnreservedRim Q' X K.reserve)
      (ordinaryUnreservedSpokes H' X Z K.reserve) ∧
    Disjoint (ordinaryPhysicalGraph D E) (spanningRestriction (ordinaryPhysicalGraph Q' H') (ordinaryInnerVertices X Z)) ∧
    Disjoint (ordinaryPhysicalGraph D E) K.reserve:=by
  intro A B φ ψ Q' H' D E
  have hsub:=ordinary_packing_physical_subhost _ _ _ r K.packing.wheels
  have hmap:=ordinary_root_free_unreserved_map Q F H X T Z W r η ell K.root_sub K.hub_sub K.cover K.reserve
  have h:=SimpleGraph.map_monotone (φ.sumMap ψ) hsub
  rw [←ordinary_physical_pair_map,←ordinary_physical_pair_map,hmap.1,hmap.2] at h
  refine ⟨h,?_,?_⟩
  · apply disjoint_iff_inf_le.mpr
    intro a b hab
    have hh:=h hab.1
    rw [ordinary_unreserved_physical_graph] at hh
    exact hh.1.2 hab.2
  · apply disjoint_iff_inf_le.mpr
    intro a b hab
    have hh:=h hab.1
    rw [ordinary_unreserved_physical_graph] at hh
    exact hh.2 hab.2
end Oberwolfach
