module

public import Oberwolfach.OrdinaryRootReferencePackingToleranceMono

@[expose] public section
/-! Increase the packing tolerance with only the equality structure needed
by the triangle certificate's local hub type. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

def ordinary_root_sharp_packing_tolerance_decEq
    (P Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (r k:ℕ) (hr:3≤r) (ηcover ell b₀ c₀ deep loss:ℝ)
    (D:OrdinaryRootCoverNonrootData Q F H X T Z W r ηcover ell)
    (α ω βparent β b B h δ εparent εstar ηsmall ηlarge ξ ζ p ε f binner c:ℝ)
    (hη:ηsmall≤ηlarge)
    (data:OrdinaryRootCoverSharpReferenceData P Q F H X T Z W r k hr ηcover ell b₀ c₀ deep loss D
      α ω βparent β b B h δ εparent εstar ηsmall ξ ζ p ε f binner c):
    OrdinaryRootCoverSharpReferenceData P Q F H X T Z W r k hr ηcover ell b₀ c₀ deep loss D
      α ω βparent β b B h δ εparent εstar ηlarge ξ ζ p ε f binner c :=by
  refine {data with static := ?_}
  have hstatic:=data.static
  refine {hstatic with balance_margin := ?_}
  exact hstatic.balance_margin.trans (mul_le_mul_of_nonneg_right hη (by positivity))
end Oberwolfach
