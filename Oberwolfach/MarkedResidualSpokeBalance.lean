module

public import Oberwolfach.BufferedResidualSpokeCardinality
public import Oberwolfach.MarkedIntervalRootCardinality

@[expose] public section
/-! Exact marked-wheel spoke balance before reserved path completion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_residual_spoke_balance
    {X V I W:Type*} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] [Fintype I]
    (m d:ℕ) (ext:∀i:I,Fin ((m+1)*d+5)↪X)
    (inner:∀i:I,Fin ((m+1)*d+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (fC:{x // x∉bufferedPathStrictInterior (fun _=> (m+1)*d) inner}↪V)
    (hcard:Fintype.card X=Fintype.card V)
    (finish:I→V)
    (hend:∀i,fC (bufferedEndpointInComplement (fun _=> (m+1)*d) ext inner hinner hdis i)=finish i)
    (R:Finset V)
    (hR:R=Finset.univ\(outsideBufferedPathImage (fun _=> (m+1)*d) inner fC ∪ Finset.univ.image finish))
    (π:Equiv.Perm W) (a:I→W)
    (hinj:∀j,Function.Injective (fun i:Fin (d+1)=>(π^i.val) (a j)))
    (hwin:∀j l:I,j≠l→Disjoint (permutationWindow π 0 d (a j))
      (permutationWindow π 0 d (a l))):
    R.card=(m+1)*(markedIntervalRootSet π (fun _=>d) a).card:=by
  have hRcard:=buffered_residual_spoke_card (fun _=> (m+1)*d) ext inner hinner hdis fC hcard finish hend R hR
  have hYcard:=marked_uniform_interval_root_card π d a hinj hwin
  simp only [Finset.sum_const_zero,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hRcard
  rw [hRcard,hYcard]
  ac_rfl
end Oberwolfach
