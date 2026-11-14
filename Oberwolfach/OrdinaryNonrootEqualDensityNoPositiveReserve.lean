module

public import Oberwolfach.OrdinaryNonrootGeometryStatic

@[expose] public section
/-! A geometry with identical parent and output density parameters cannot
accommodate a positive reserve. This identifies the required strict gap. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_nonroot_equal_density_no_positive_reserve
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (r k:ℕ) (ω β b B εparent εstar η ξ ζ p ε f binner c:ℝ) (X:Finset V) (Z:Finset U)
    (hgeom:OrdinaryNonrootGeometryStatic r k ω β β b B εparent εstar η ξ ζ p ε f binner c X Z)
    (hξ:0<ξ):False :=by
  have hdeg:=hgeom.degree_margin
  have hζ:=hgeom.zeta_nonneg
  linarith
end Oberwolfach
