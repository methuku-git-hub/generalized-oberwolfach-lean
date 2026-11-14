module

public import Oberwolfach.OrdinaryGeneralHubConditionsFromCleanup

@[expose] public section
/-! The same cleanup profile supplies hub-class sizes and common
neighborhoods relative to the actual inner set, with no ambient ratio. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_general_relative_hub_conditions_from_cleanup
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (γ pR pH density tR tH Ledit βe βh:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s j σ)
    (hA:A.Nonempty) (hscale:γ*A.card≤βe*Fintype.card (V⊕U)):
    (∀j:{u:U // u∉Z},γ*A.card≤((ordinaryBoundaryHubSet H Z A j).card:ℝ)) ∧
    (∀j:{u:U // u∉Z},∀S:Finset V,S⊆ordinaryBoundaryHubSet H Z A j→S.card≤2→
      γ*A.card≤((common (ordinaryBoundaryHubSet H Z A j) S
        (fun x=>(spanningRestriction Q A).neighborFinset x)).card:ℝ)):=by
  have hn:0<Fintype.card V:=Fintype.card_pos_iff.mpr ⟨hA.choose⟩
  have hnR:0<(Fintype.card V:ℝ):=by exact_mod_cast hn
  let c:ℝ:=βe*Fintype.card (V⊕U)/Fintype.card V
  have hc:c*Fintype.card V=βe*Fintype.card (V⊕U):=by
    dsimp [c]
    exact div_mul_cancel₀ _ (ne_of_gt hnR)
  have hrel:γ*A.card≤c*Fintype.card V:=by rw [hc];exact hscale
  have hconditions:=ordinary_general_hub_conditions_from_cleanup P Q F H A Z π d j s c c
    pR pH density tR tH Ledit βe βh σ profile hA (le_of_eq hc) (le_of_eq hc)
  constructor
  · intro j
    have hh:=(hconditions.1 j)
    convert hrel.trans hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro j S hS hcard
    have hh:=hconditions.2 j S hS hcard
    convert hrel.trans hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
