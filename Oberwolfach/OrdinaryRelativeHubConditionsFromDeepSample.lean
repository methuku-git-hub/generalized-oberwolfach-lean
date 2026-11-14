module

public import Oberwolfach.OrdinaryHubConditionsFromDeepSample

@[expose] public section
/-! The deeper sampled rows also give three-neighbor geometry on the
inner-domain scale, including the triangle-factor case. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_relative_hub_conditions_from_deep_sample
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (γ p pR pH density tR tH L Ledit βe βh ε:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A B pR pH density tR tH Ledit βe βh s j σ)
    (deep:RawOrdinaryRows P π d 3 A pR s j tR σ)
    (hA:A.Nonempty)
    (hp:0<p) (hp1:p≤1) (hpR:p≤pR) (hpH:p≤pH) (hdensity:(3/4:ℝ)≤density)
    (hL:0≤L) (hLedit:0≤Ledit) (hLA:L≤(A.card:ℝ)/24) (hF:∀v,(F.degree v:ℝ)≤L)
    (hbudget:tR+4*Ledit≤ε*A.card) (hε:ε≤p^4/16) (hγ:γ≤p^4/16):
    (∀j:{u:U // u∉B},γ*A.card≤((ordinaryBoundaryHubSet H B A j).card:ℝ)) ∧
    (∀j:{u:U // u∉B},∀S:Finset V,S⊆ordinaryBoundaryHubSet H B A j→S.card≤3→
      γ*A.card≤((common (ordinaryBoundaryHubSet H B A j) S
        (fun x=>(spanningRestriction Q A).neighborFinset x)).card:ℝ)):=by
  have hn:0<Fintype.card V:=Fintype.card_pos_iff.mpr ⟨hA.choose⟩
  have hnR:0<(Fintype.card V:ℝ):=by exact_mod_cast hn
  let c:ℝ:=(p^4/16)*A.card/Fintype.card V
  have hc:c*Fintype.card V=(p^4/16)*A.card:=by
    dsimp [c]
    exact div_mul_cancel₀ _ (ne_of_gt hnR)
  have hrel:γ*A.card≤c*Fintype.card V:=by
    rw [hc]
    exact mul_le_mul_of_nonneg_right hγ (Nat.cast_nonneg _)
  have hh:=ordinary_hub_conditions_from_deep_sample P Q F H A B π d j s c c p pR pH density
    tR tH L Ledit βe βh ε σ profile deep hp hp1 hpR hpH hdensity hL hLedit hLA hF hbudget hε
    (le_of_eq hc) (le_of_eq hc)
  exact ⟨fun j=>hrel.trans (hh.1 j),fun j S hS hcard=>hrel.trans (hh.2 j S hS hcard)⟩
end Oberwolfach
