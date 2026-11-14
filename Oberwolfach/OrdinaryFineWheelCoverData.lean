module

public import Oberwolfach.OrdinaryFineWheelCoverResult
public import Oberwolfach.OrdinaryRootCoverFineDataFromPacking

@[expose] public section
/-! The same selected cover supplies both the standard root data and the
small cross error into its inner nonroot pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [LinearOrder U]

theorem ordinary_fine_wheel_cover_data
    (m K:ℕ) (ξ aLoad:ℝ) (Q F:SimpleGraph V) (H:V→U→Prop)
    (I T:Finset V) (B W:Finset U) (hTI:T⊆I) (hWB:W⊆B)
    (hcover:OrdinaryFineWheelCoverResult m K ξ aLoad Q F H I T B W):
    let ell:=max (18*aLoad*Fintype.card V+3*((W.card:ℝ)+(K+1)*T.card))
      (3*aLoad*Fintype.card V*(m+1)+(T.card:ℝ)*(m+1));
    ∃D:OrdinaryRootCoverNonrootData Q F H I T B W (m+1) (10*ξ*I.card) ell,
      ∀v,|((D.rim.neighborFinset v∩(I\T)).card:ℝ)-2*((B\W).filter (D.spokes v)).card|≤12*aLoad*Fintype.card V:=by
  intro ell
  obtain ⟨D,J,hD,hDdeep,hJ,hbalance,hdiv,hdegree,M,hdis,hE,hRcover,hSrow,hScol,hleft,hright,hcross,havoid⟩:=hcover
  exact ordinary_root_cover_fine_data_from_corrected_packing Q D F H J I T B W (m+1) (10*ξ*I.card) ell
    hTI hWB hDdeep (by intro v u h;exact (hJ v u h).2) hdegree M hdis hE hRcover hSrow hScol
    (by intro v hv;exact (hleft v hv).trans (le_max_left _ _))
    (by intro u hu;exact (hright u hu).trans (le_max_right _ _))
    (12*aLoad*Fintype.card V) hcross
end Oberwolfach
