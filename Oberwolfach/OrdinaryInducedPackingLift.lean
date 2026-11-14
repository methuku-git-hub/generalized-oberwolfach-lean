module

public import Oberwolfach.OrdinaryHostDecompositionEmbedding
public import Oberwolfach.OrdinaryEmbeddedDecompositions
public import Oberwolfach.RowCoverUnion

@[expose] public section
/-! Lift a selected physical wheel packing into the original host without
changing its edge-disjointness or forbidden-pair condition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U':Type} [Fintype V] [Fintype U] [Fintype V'] [Fintype U']
  [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']

theorem ordinary_induced_packing_lift_decomposition
    (G FG:SimpleGraph V) (HG:V→U→Prop) (Q F:SimpleGraph V') (H:V'→U'→Prop) (r:ℕ)
    (φ:V↪V') (ψ:U↪U')
    (hQ:∀v w,G.Adj v w→Q.Adj (φ v) (φ w))
    (hH:∀v u,HG v u→H (φ v) (ψ u))
    (hF:∀v w,F.Adj (φ v) (φ w)→FG.Adj v w)
    (M:Finset (OrdinaryWheel G FG HG r))
    (hM:∀A∈M,∀B∈M,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B)):
    let D:=(ordinaryWheelRimGraph M).map φ;
    let E:=ordinaryMappedSpokes (ordinaryPackingSpokes M) φ ψ;
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources D E) ∧
    HasOrdinaryWheelDecomposition D E r:=by
  intro D E
  have hsource:HasResourceDecomposition (ordinaryWheelResources (P:=G) (F:=FG) (Hbase:=HG) (r:=r))
      (ordinaryHostResources (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)):=
    ⟨M,hM,ordinaryPacking_resources M⟩
  exact ⟨ordinary_host_decomposition_embedding G FG (ordinaryWheelRimGraph M) HG (ordinaryPackingSpokes M)
    Q F H r φ ψ hQ hH hF hsource,
    ordinary_decomposition_embedding (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M) r φ ψ
      (ordinaryPacking_decomposition M hM)⟩
end Oberwolfach
