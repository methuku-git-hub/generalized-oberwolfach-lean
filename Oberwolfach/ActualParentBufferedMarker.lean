module

public import Oberwolfach.ActualPrescribedBufferedMarkers

@[expose] public section
/-! Read the original buffered parent markers at their exact c-spaced indices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_parent_buffered_marker
    {X K J:Type} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (ext:∀i:K,Fin (data.c*data.d+5)↪X)
    (hsupp:∀i∈data.s₁∪data.s₂,(data.P i).support=List.ofFn (ext i))
    (i:K) (hi:i∈data.s₁∪data.s₂) (j:Fin (data.d+1)):
    (data.P i).getVert (2+data.c*j.val)=bufferedMarker data.c data.d (ext i) j:=by
  have hj:j.val≤data.d:=by have hh:=j.isLt;omega
  have hm:=Nat.mul_le_mul_left data.c hj
  have hh:some ((data.P i).getVert (2+data.c*j.val))=(data.P i).support[2+data.c*j.val]? :=
    (data.P i).getVert_eq_support_getElem? (by rw [data.hlen i hi];omega)
  rw [hsupp i hi] at hh
  simpa only [List.getElem?_ofFn,dif_pos (show 2+data.c*j.val<data.c*data.d+5 by omega),Option.some.injEq,
    bufferedMarker] using hh
end Oberwolfach
