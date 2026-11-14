module

public import Oberwolfach.OrdinaryCleanupMarginExplicit
public import Oberwolfach.OrdinaryCleanupFixedMarginsProperty

@[expose] public section
/-! The cleanup margins have explicit dependence on the domain ratio. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_cleanup_fixed_margins_explicit
    (p₀ δ a K:ℝ) (hp₀:0<p₀) (hδ:0<δ) (ha:0<a) (hK:0<K):
    OrdinaryCleanupFixedMarginsProperty p₀ δ a K (p₀^3*δ/(4*K)) (p₀^2*a/(4*K)) :=by
  intro V U Γ Color _ _ _ _ _ _ P Q F H π d X Z pR pH density tR tH L βeOld βhOld s j raw hprofile
    hsize hZ hpR hpH hdensity htR hLe htH hLh
  obtain ⟨he,hh⟩:=ordinary_cleanup_margin_explicit p₀ δ a K hp₀ hδ ha hK
    (Fintype.card (V⊕U)) X.card Z.card pR pH density tR tH L
    (by positivity) hsize hZ hpR hpH hdensity htR hLe htH hLh
  exact ordinary_cleanup_profile_replace_margins P Q F H π d X Z pR pH density tR tH L βeOld βhOld
    (p₀^3*δ/(4*K)) (p₀^2*a/(4*K)) s j raw hprofile he hh
end Oberwolfach
