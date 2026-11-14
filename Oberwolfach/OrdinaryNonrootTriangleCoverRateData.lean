module

public import Oberwolfach.OrdinaryNonrootTriangleCoverRateResult
public import Oberwolfach.OrdinaryRootCoverNonrootDataFromPacking

@[expose] public section
/-! Feed the same corrected triangle root packing, with its next-level
cost, into the protected cleanup and fresh-factor construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [LinearOrder U]

theorem ordinary_nonroot_triangle_cover_rate_data
    (ξ δ:ℝ) (Q F:SimpleGraph V) (H:V→U→Prop) (I T:Finset V) (B W:Finset U)
    (hTI:T⊆I) (hWB:W⊆B)
    (hcover:OrdinaryNonrootTriangleCoverRateResult ξ δ Q F H I T B W):
    Nonempty (OrdinaryRootCoverNonrootData Q F H I T B W 3 (10*ξ*I.card) (δ*I.card)) :=by
  obtain ⟨D,J,hD,hDdeep,hJ,hbalance,hdiv,hdegree,M,hdis,hE,hRcover,hSrow,hScol,hleft,hright,havoid⟩:=hcover
  exact ordinary_root_cover_nonroot_data_from_corrected_packing Q D F H J I T B W 3 (10*ξ*I.card) (δ*I.card)
    hTI hWB hDdeep (by intro v u h;exact (hJ v u h).2) hdegree M hdis hE hRcover hSrow hScol hleft hright
end Oberwolfach
