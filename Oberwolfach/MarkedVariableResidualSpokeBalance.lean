module

public import Oberwolfach.MarkedResidualSpokeBalance

@[expose] public section
/-! Exact residual-spoke balance for the original variable interval lengths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_variable_residual_spoke_balance
    {X V I W:Type*} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] [Fintype I]
    (c:ℕ) (k:I→ℕ) (ext:∀i:I,Fin (c*k i+5)↪X)
    (inner:∀i:I,Fin (c*k i+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (fC:{x // x∉bufferedPathStrictInterior (fun i=>c*k i) inner}↪V)
    (hcard:Fintype.card X=Fintype.card V)
    (finish:I→V)
    (hend:∀i,fC (bufferedEndpointInComplement (fun i=>c*k i) ext inner hinner hdis i)=finish i)
    (R:Finset V)
    (hR:R=Finset.univ\(outsideBufferedPathImage (fun i=>c*k i) inner fC ∪ Finset.univ.image finish))
    (π:Equiv.Perm W) (a:I→W)
    (hinj:∀j,Function.Injective (fun i:Fin (k j+1)=>(π^i.val) (a j)))
    (hwin:∀j l:I,j≠l→Disjoint (permutationWindow π 0 (k j) (a j))
      (permutationWindow π 0 (k l) (a l))):
    R.card=c*(markedIntervalRootSet π k a).card:=by
  have hRcard:=buffered_residual_spoke_card (fun i=>c*k i) ext inner hinner hdis fC hcard finish hend R hR
  have hYcard:=marked_interval_root_card π k a hinj hwin
  rw [hRcard,hYcard,Finset.mul_sum]
end Oberwolfach
