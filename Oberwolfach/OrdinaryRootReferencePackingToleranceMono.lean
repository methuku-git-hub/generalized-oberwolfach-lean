module

public import Oberwolfach.OrdinaryRootCoverReferenceData
public import Oberwolfach.OrdinaryRootCoverSharpReferenceExists

@[expose] public section
/-! The packing tolerance in the static root reference may be increased.
This allows a positive tolerance fixed before the conflict size to be reused
when a later certificate chooses a larger tolerance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [LinearOrder U]

theorem ordinary_nonroot_geometry_static_packing_tolerance_mono
    (r k:ℕ) (ω βparent β b B εparent εstar ηsmall ηlarge ξ ζ p ε f binner c:ℝ)
    (X:Finset V) (Z:Finset U) (hη:ηsmall≤ηlarge)
    (h:OrdinaryNonrootGeometryStatic r k ω βparent β b B εparent εstar ηsmall ξ ζ p ε f binner c X Z):
    OrdinaryNonrootGeometryStatic r k ω βparent β b B εparent εstar ηlarge ξ ζ p ε f binner c X Z :=by
  refine {h with balance_margin := ?_}
  exact h.balance_margin.trans (mul_le_mul_of_nonneg_right hη (by positivity))

def ordinary_root_cover_reference_packing_tolerance_mono
    (P Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (r k:ℕ) (hr:3≤r) (ηcover ell b₀ c₀:ℝ)
    (D:OrdinaryRootCoverNonrootData Q F H X T Z W r ηcover ell)
    (α ω βparent β b B h δ εparent εstar ηsmall ηlarge ξ ζ p ε f binner c:ℝ)
    (hη:ηsmall≤ηlarge)
    (data:OrdinaryRootCoverReferenceData P Q F H X T Z W r k hr ηcover ell b₀ c₀ D
      α ω βparent β b B h δ εparent εstar ηsmall ξ ζ p ε f binner c):
    OrdinaryRootCoverReferenceData P Q F H X T Z W r k hr ηcover ell b₀ c₀ D
      α ω βparent β b B h δ εparent εstar ηlarge ξ ζ p ε f binner c :=by
  refine {data with static := ?_}
  exact ordinary_nonroot_geometry_static_packing_tolerance_mono r k ω βparent β b B εparent εstar
    ηsmall ηlarge ξ ζ p ε f binner c _ _ hη data.static
def ordinary_root_cover_sharp_reference_packing_tolerance_mono
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
  exact ordinary_nonroot_geometry_static_packing_tolerance_mono r k ω βparent β b B εparent εstar
    ηsmall ηlarge ξ ζ p ε f binner c _ _ hη data.static

theorem ordinary_root_cover_sharp_reference_exists_packing_tolerance_mono
    (P Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (r k:ℕ) (hr:3≤r) (cover ell bin cin deep loss α ω βparent β b B h δ εparent εstar ηsmall ηlarge ξ ζ p ε f binner c:ℝ)
    (hη:ηsmall≤ηlarge)
    (hex:OrdinaryRootCoverSharpReferenceExists P Q F H X T Z W r k hr cover ell bin cin deep loss
      α ω βparent β b B h δ εparent εstar ηsmall ξ ζ p ε f binner c):
    OrdinaryRootCoverSharpReferenceExists P Q F H X T Z W r k hr cover ell bin cin deep loss
      α ω βparent β b B h δ εparent εstar ηlarge ξ ζ p ε f binner c :=by
  obtain ⟨D,⟨data⟩⟩:=hex
  exact ⟨D,⟨ordinary_root_cover_sharp_reference_packing_tolerance_mono P Q F H X T Z W r k hr cover ell bin cin deep loss D
    α ω βparent β b B h δ εparent εstar ηsmall ηlarge ξ ζ p ε f binner c hη data⟩⟩
end Oberwolfach
