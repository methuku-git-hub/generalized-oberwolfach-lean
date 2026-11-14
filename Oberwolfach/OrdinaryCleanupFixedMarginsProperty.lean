module

public import Oberwolfach.OrdinaryCleanupFixedMarginsHierarchy

@[expose] public section
/-! Name the fixed cleanup-margin property for later parameter choices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryCleanupFixedMarginsProperty (p₀ δ a K βe βh:ℝ):Prop :=
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U],
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ) (X:Finset V) (Z:Finset U)
      (pR pH density tR tH L βeOld βhOld:ℝ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color),
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH L βeOld βhOld s j raw→
    (Fintype.card (V⊕U):ℝ)≤K*X.card→a*X.card≤(Z.card:ℝ)→p₀≤pR→p₀≤pH→(1/2:ℝ)+δ≤density→
    tR≤(p₀^3*δ)*X.card/4→3*L≤(p₀^3*δ)*X.card/4→
    tH≤(p₀^2*a)*X.card/4→2*L≤(p₀^2*a)*X.card/4→
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH L βe βh s j raw

theorem ordinary_cleanup_fixed_margins_property
    (p₀ δ a K:ℝ) (hp₀:0<p₀) (hδ:0<δ) (ha:0<a) (hK:0<K):
    ∃βe βh:ℝ,0<βe ∧ 0<βh ∧ OrdinaryCleanupFixedMarginsProperty p₀ δ a K βe βh :=by
  exact ordinary_cleanup_fixed_margins_hierarchy p₀ δ a K hp₀ hδ ha hK
end Oberwolfach
