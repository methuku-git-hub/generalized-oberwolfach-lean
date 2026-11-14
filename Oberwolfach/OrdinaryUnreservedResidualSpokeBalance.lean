module

public import Oberwolfach.MarkedVariableResidualSpokeBalanceReserve
public import Oberwolfach.OrdinaryUnreservedFactorCardinality
public import Oberwolfach.BufferedResidualSpokeCardinalityReserve

@[expose] public section
/-! Exact residual-spoke balance for the original variable interval lengths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_unreserved_residual_spoke_balance
    {n r:ℕ} {I W:Type*} [Fintype W] [DecidableEq W] [Fintype I]
    (F:SimpleGraph (Fin n)) (Cres:Finset F.ConnectedComponent)
    (hsize:∀c:↥Cres,Fintype.card c.val=r):
    let X:={x:Fin n // F.connectedComponentMk x∉Cres};
    ∀(c:ℕ) (k:I→ℕ) (ext:∀i:I,Fin (c*k i+5)↪X)
    (inner:∀i:I,Fin (c*k i+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (fC:{x // x∉bufferedPathStrictInterior (fun i=>c*k i) inner}↪Fin n)
        (finish:I→Fin n)
    (hend:∀i,fC (bufferedEndpointInComplement (fun i=>c*k i) ext inner hinner hdis i)=finish i)
    (R:Finset (Fin n))
    (hR:R=Finset.univ\(outsideBufferedPathImage (fun i=>c*k i) inner fC ∪ Finset.univ.image finish))
    (π:Equiv.Perm W) (a:I→W)
    (hinj:∀j,Function.Injective (fun i:Fin (k j+1)=>(π^i.val) (a j)))
    (hwin:∀j l:I,j≠l→Disjoint (permutationWindow π 0 (k j) (a j))
      (permutationWindow π 0 (k l) (a l))),
    R.card=r*Cres.card+c*(markedIntervalRootSet π k a).card:=by
  intro X c k ext inner hinner hdis fC finish hend R hR π a hinj hwin
  have hcard:Fintype.card X+r*Cres.card=Fintype.card (Fin n):=by
    simpa only [X,Fintype.card_fin] using ordinary_unreserved_factor_cardinality F Cres hsize
  exact marked_variable_residual_spoke_balance_with_reserve c k ext inner hinner hdis fC (r*Cres.card) hcard finish hend R hR π a hinj hwin
end Oberwolfach
