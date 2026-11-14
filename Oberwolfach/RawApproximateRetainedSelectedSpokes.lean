module

public import Oberwolfach.MarkedOccupiedAvoidsOuter

@[expose] public section
/-! The raw approximate and retained selected spoke classes are physically
disjoint, even though thinning may reveal new selected ordinary labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem raw_approximate_spoke_avoids_retained_selected
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀ g₂:Γ) (hg:g₂≠g₀) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t)
    (j₁ j₂:Color) (hj:j₂≠j₁) (v:V) (u:U) (b b':Bool):
    ¬(rawMarkedSpokes π d σ g₂ j₂ b v u ∧
      retainedRawMarkedSpokes π d σ g₀ t J g₀ j₁ b' v u):=by
  rintro ⟨ha,hb⟩
  have ha':retainedRawMarkedSpokes π d σ g₀ t J g₂ j₂ b v u:=by
    cases b with
    | false=>exact raw_ordinary_spoke_survives_start_retention π d σ g₀ t J g₂ j₂ v u ha
    | true=>exact raw_other_marked_spoke_survives_start_retention π d σ g₀ t J g₂ hg j₂ v u ha
  cases b <;> cases b'
  · change retainedRawFamilyState π d σ g₀ t J (v,u)=some (Sum.inr j₂) at ha'
    change retainedRawFamilyState π d σ g₀ t J (v,u)=some (Sum.inr j₁) at hb
    apply hj
    simpa only [Option.some.injEq,Sum.inr.injEq] using ha'.symm.trans hb
  · change retainedRawFamilyState π d σ g₀ t J (v,u)=some (Sum.inr j₂) at ha'
    change retainedRawFamilyState π d σ g₀ t J (v,u)=some (Sum.inl g₀) at hb
    cases ha'.symm.trans hb
  · change retainedRawFamilyState π d σ g₀ t J (v,u)=some (Sum.inl g₂) at ha'
    change retainedRawFamilyState π d σ g₀ t J (v,u)=some (Sum.inr j₁) at hb
    cases ha'.symm.trans hb
  · change retainedRawFamilyState π d σ g₀ t J (v,u)=some (Sum.inl g₂) at ha'
    change retainedRawFamilyState π d σ g₀ t J (v,u)=some (Sum.inl g₀) at hb
    apply hg
    simpa only [Option.some.injEq,Sum.inl.injEq] using ha'.symm.trans hb
end Oberwolfach
