module

public import Oberwolfach.OrdinaryUnreservedFactorCardinality
public import Oberwolfach.ActualResidualSizeLower

@[expose] public section
/-! Account exactly for the reserved component vertices when applying the
general residual-size lower bound to the unreserved factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_unreserved_residual_size_lower
    {n r:ℕ} {A B J:Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [DecidableEq J]
    (F:SimpleGraph (Fin n)) (C:Finset F.ConnectedComponent)
    (hsize:∀c:↥C,Fintype.card c.val=r):
    let S:Set (Fin n):={x | F.connectedComponentMk x∉C};
    ∀a:ActualResidualData (K:=A⊕B) (J:=J) (F.induce S),
      a.s₁=firstSumIndices→a.s₂=secondSumIndices→
      n≤r*C.card+a.remaining.card+(a.t.biUnion (fun j=>(a.C j).support.toFinset)).card+
        (a.c*a.d-1)*Fintype.card (A⊕B):=by
  intro S a hs₁ hs₂
  have hh:=actual_residual_size_lower_sum_indices a hs₁ hs₂
  have hc:=ordinary_unreserved_factor_cardinality F C hsize
  change Fintype.card S+r*C.card=n at hc
  omega
end Oberwolfach
