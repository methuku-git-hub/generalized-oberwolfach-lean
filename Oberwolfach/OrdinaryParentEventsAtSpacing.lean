module

public import Oberwolfach.OrdinaryParentReferenceDeepJointBeforeSpacingAt

@[expose] public section
/-! Specialize the fixed parent parameters to the spacing chosen later by
the original matching construction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def OrdinaryParentEventsAtSpacing
    (m k d:ℕ) (hm:3≤m) (hd:2≤d) (α ρ₀ pstar βP ηP row ηH βH c B δ h ε:ℝ) (hp:0<pstar):Prop :=
    ∀χhost χcut:ℝ,0<χhost→0<χcut→
    ∃εTri βmax:ℝ,0<εTri ∧ 0<βmax ∧ βmax≤1/4 ∧ βmax≤α/4 ∧ βmax≤εTri ∧
    ∃Mhost Mcut:ℕ,1≤Mhost ∧ 1≤Mcut ∧
      OrdinaryGeneralFixedDomainSelector m k d Mhost hm hd (max (1/2) (cycleThreshold (m+1))) α pstar (ρ₀/16)
        βP ηP row ηH βH c B εTri ε χhost (2*(3*d)) hp ∧
      OrdinaryReferenceCutsDomainSelector d Mcut hd α pstar (ρ₀/16) δ h ε χcut (2*(3*d))

theorem ordinary_parent_events_at_spacing
    (m k:ℕ) (hm:3≤m) (α ρ₀ pstar βP ηP row ηH βH c B δ h ε:ℝ) (hp:0<pstar)
    (hε:0<ε) (hε1:ε<1)
    (hparent:∀(d:ℕ) (hd:2≤d) (ε' χhost χcut:ℝ),0<ε'→ε'<1→0<χhost→0<χcut→
      ∃εTri βmax:ℝ,0<εTri ∧ 0<βmax ∧ βmax≤1/4 ∧ βmax≤α/4 ∧ βmax≤εTri ∧
      ∃Mhost Mcut:ℕ,1≤Mhost ∧ 1≤Mcut ∧
        OrdinaryGeneralFixedDomainSelector m k d Mhost hm hd (max (1/2) (cycleThreshold (m+1))) α pstar (ρ₀/16)
          βP ηP row ηH βH c B εTri ε' χhost (2*(3*d)) hp ∧
        OrdinaryReferenceCutsDomainSelector d Mcut hd α pstar (ρ₀/16) δ h ε' χcut (2*(3*d))):
    ∀(d:ℕ) (hd:2≤d),OrdinaryParentEventsAtSpacing m k d hm hd α ρ₀ pstar βP ηP row ηH βH c B δ h ε hp :=by
  intro d hd χhost χcut hχhost hχcut
  exact hparent d hd ε χhost χcut hε hε1 hχhost hχcut
end Oberwolfach
