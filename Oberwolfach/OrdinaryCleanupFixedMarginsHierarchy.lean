module

public import Oberwolfach.OrdinaryCleanupMarginHierarchy
public import Oberwolfach.OrdinaryCleanupProfileReplaceMargins

@[expose] public section
/-! Fix the extension margins before later edit tolerances, then recover
    them on any actual profile satisfying the stated scale bounds. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_cleanup_fixed_margins_hierarchy
    (p₀ δ a K:ℝ) (hp₀:0<p₀) (hδ:0<δ) (ha:0<a) (hK:0<K):
    ∃βe βh:ℝ,0<βe ∧ 0<βh ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U],
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ) (X:Finset V) (Z:Finset U)
      (pR pH density tR tH L βeOld βhOld:ℝ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color),
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH L βeOld βhOld s j raw→
    (Fintype.card (V⊕U):ℝ)≤K*X.card→a*X.card≤(Z.card:ℝ)→p₀≤pR→p₀≤pH→(1/2:ℝ)+δ≤density→
    tR≤(p₀^3*δ)*X.card/4→3*L≤(p₀^3*δ)*X.card/4→
    tH≤(p₀^2*a)*X.card/4→2*L≤(p₀^2*a)*X.card/4→
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH L βe βh s j raw :=by
  obtain ⟨βe,βh,hβe,hβh,hmargin⟩:=ordinary_cleanup_margin_hierarchy p₀ δ a K hp₀ hδ ha hK
  refine ⟨βe,βh,hβe,hβh,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P Q F H π d X Z pR pH density tR tH L βeOld βhOld s j raw hprofile
    hsize hZ hpR hpH hdensity htR hLe htH hLh
  obtain ⟨he,hh⟩:=hmargin (Fintype.card (V⊕U)) X.card Z.card pR pH density tR tH L
    (by positivity) hsize hZ hpR hpH hdensity htR hLe htH hLh
  exact ordinary_cleanup_profile_replace_margins P Q F H π d X Z pR pH density tR tH L βeOld βhOld βe βh s j raw hprofile he hh
end Oberwolfach
