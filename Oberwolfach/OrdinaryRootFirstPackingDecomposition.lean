module

public import Oberwolfach.OrdinaryRootFirstPackingContext
public import Oberwolfach.OrdinaryInducedPackingLift

@[expose] public section
/-! The nonroot packing lifts to actual wheel decompositions in the
post-root-cover host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_packing_decomposition
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t:ℝ)
    (K:OrdinaryRootFirstPackingContext Q F H X T Z W r η ell t):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    let φ:A↪V:=⟨Subtype.val,Subtype.val_injective⟩;
    let ψ:B↪U:=⟨Subtype.val,Subtype.val_injective⟩;
    let Q':=Q\K.cover.rim;let H':=fun v u=>H v u∧¬K.cover.spokes v u;
    let D:=(ordinaryWheelRimGraph K.packing.wheels).map φ;
    let E:=ordinaryMappedSpokes (ordinaryPackingSpokes K.packing.wheels) φ ψ;
    HasResourceDecomposition (ordinaryWheelResources (P:=Q') (F:=F) (Hbase:=H') (r:=r)) (ordinaryHostResources D E) ∧
      HasOrdinaryWheelDecomposition D E r:=by
  intro A B φ ψ Q' H' D E
  apply ordinary_induced_packing_lift_decomposition _ _ _ Q' F H' r φ ψ ?_ ?_ ?_ K.packing.wheels K.packing.disjoint
  · intro v w hvw
    exact hvw.1.1
  · intro v u hvu
    exact hvu.1
  · intro v w hvw
    exact hvw
end Oberwolfach
