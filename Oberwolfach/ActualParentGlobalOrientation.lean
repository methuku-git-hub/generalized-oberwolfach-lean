module

public import Oberwolfach.FactorOrientationGlobalReservedBlocks
public import Oberwolfach.ResidualActualData

@[expose] public section
/-! An actual parent walk with the original reserved block support follows the
globally aligned factor orientation at every step. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem parent_walk_follows_global_reserved_orientation
    {X I:Type} [Fintype X] [DecidableEq X] [Fintype I]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (components:I↪G.ConnectedComponent)
    (E:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (c d:ℕ) (q:LongReservedBlockIndex G components c d) (t:ℕ) (ht:t≤d)
    {u v:X} (p:G.Walk u v) (hlen:p.length=c*t+4)
    (hsupp:p.support=List.ofFn (longReservedSigmaBlock G components c d (fun i=>E (components i)) q t ht)):
    ∀k<p.length,factorCycleOrientation G E (p.getVert k)=p.getVert (k+1):=by
  intro k hk
  let block:=longReservedSigmaBlock G components c d (fun i=>E (components i)) q t ht
  have hv:∀j:ℕ,(hj:j≤c*t+4)→p.getVert j=block ⟨j,by omega⟩:=by
    intro j hj
    have hh:some (p.getVert j)=p.support[j]? :=p.getVert_eq_support_getElem? (by omega)
    rw [hsupp] at hh
    simpa only [List.getElem?_ofFn,dif_pos (show j<c*t+5 by omega),Option.some.injEq] using hh
  have hk':k<c*t+4:=by simpa [hlen] using hk
  rw [hv k (by omega),hv (k+1) (by omega)]
  exact factor_cycle_orientation_reserved_block_step_from_global G hG components E c d q t ht ⟨k,hk'⟩
end Oberwolfach
