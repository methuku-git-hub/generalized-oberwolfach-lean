module

public import Oberwolfach.OrdinaryNonrootWheelCoverResult
public import Oberwolfach.OrdinaryRootCoverNonrootDataFromDeepBounds

@[expose] public section
/-! The common-sample root cover supplies the protected data consumed by
the later cleanup and pairing construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [LinearOrder U]

theorem ordinary_nonroot_wheel_cover_data
    (m K:ℕ) (ξ aLoad:ℝ) (Q F:SimpleGraph V) (H:V→U→Prop)
    (I T:Finset V) (B W:Finset U) (hTI:T⊆I) (hWB:W⊆B)
    (hcover:OrdinaryNonrootWheelCoverResult m K ξ aLoad Q F H I T B W):
    Nonempty (OrdinaryRootCoverNonrootData Q F H I T B W (m+1) (10*ξ*I.card)
      (max (18*aLoad*Fintype.card V+3*((W.card:ℝ)+(K+1)*T.card))
        (3*aLoad*Fintype.card V*(m+1)+(T.card:ℝ)*(m+1)))):=by
  obtain ⟨D,J,hD,hDdeep,hJ,hbalance,hdiv,hdegree,M,hdis,hE,hRcover,hSrow,hScol,hleft,hright,havoid⟩:=hcover
  apply ordinary_root_cover_nonroot_data_from_deep_bounds m K aLoad ξ Q D F H J I T B W hTI hWB hDdeep
    (by intro v u h;exact (hJ v u h).2) hdegree M hdis hE hRcover hSrow hScol hleft hright
end Oberwolfach
