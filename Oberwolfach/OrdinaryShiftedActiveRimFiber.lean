module

public import Oberwolfach.OrdinaryPhysicalEligibility
public import Oberwolfach.OrdinaryShiftedMarkedResourceState

@[expose] public section
/-! A physical eligible directed rim edge activates exactly its unshifted
and shifted typed representations in the ordinary sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_shifted_active_rim_oriented
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (g:Γ) (j:Color)
    (σ:RawMarkedOutcome V U Γ Color) (x y:V) (hP:P.Adj x y)
    (hfar:¬PermutationClose π (3*d+2) x y)
    (hstate:σ (Sum.inl s(x,y))=some (false,orientationBit x y)):
    let st:=typedMarkedResourceState (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j);
    st (Sum.inl (Sum.inl (x,y)))=true ∧
    st (Sum.inl (Sum.inl (y,x)))=false ∧
    st (Sum.inl (Sum.inr (x,π.symm y)))=true ∧
    st (Sum.inl (Sum.inr (y,π.symm x)))=false :=by
  intro st
  obtain ⟨h1,h2,h3⟩:=ordinary_physical_far_auxiliary π d x y hfar
  have h4:¬PermutationClose π (3*d) y x:=fun h=>h1 ((permutationClose_symm π _ _ _).mp h)
  have hb:orientationBit x y≠orientationBit y x:=orientationBit_ne_swap x y hP.ne
  have hs:σ (Sum.inl s(y,x))=some (false,orientationBit x y):=by
    rw [show s(y,x)=s(x,y) from Sym2.eq_swap]
    exact hstate
  have hforward:σ (Sum.inl s(x,π (π.symm y)))=some (false,orientationBit x y):=by
    have he:s(x,π (π.symm y))=s(x,y):=by rw [Equiv.apply_symm_apply]
    exact (congrArg (fun e:Sym2 V=>σ (Sum.inl e)) he).trans hstate
  have hback:σ (Sum.inl s(y,π (π.symm x)))=some (false,orientationBit x y):=by
    have he:s(y,π (π.symm x))=s(y,x):=by rw [Equiv.apply_symm_apply]
    exact (congrArg (fun e:Sym2 V=>σ (Sum.inl e)) he).trans hs
  dsimp [st,typedMarkedResourceState,ordinaryShiftedPairRims]
  simp [h1,h2,h3,h4,hP,hP.symm,hstate,hs,hforward,hback,hb,Ne.symm hb]
end Oberwolfach
