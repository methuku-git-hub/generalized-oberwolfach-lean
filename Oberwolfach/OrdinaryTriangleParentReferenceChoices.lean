module

public import Oberwolfach.OrdinaryTriangleReferenceEventHierarchy

@[expose] public section
/-! Choose the full-parent triangle weights and joint reference cuts before
the host, retaining their callbacks for later sampling tolerances. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleParentReferenceChoices
    (d:ℕ) (hd:2≤d) (α ρ₀ pstar ηP:ℝ) (hα:0<α) (hp:0<pstar):Prop :=
    ∃(δ h βP:ℝ) (k:ℕ) (βH c B:ℝ),0<δ ∧ δ<1/4 ∧ 0<h ∧ 0<βP ∧
      5≤k ∧ ordinaryTrianglePackingThreshold α hα≤k ∧ 0<βH ∧ 0<c ∧ 0<B ∧
    ∀(ηH ε χtri χcut:ℝ),0<ηH→0<ε→ε<1→0<χtri→0<χcut→
    ∃εTri βmax:ℝ,0<εTri ∧ 0<βmax ∧ βmax≤1/4 ∧ βmax≤α/4 ∧ βmax≤εTri ∧
    ∃Mtri Mcut:ℕ,1≤Mtri ∧ 1≤Mcut ∧
      OrdinaryTriangleFixedDomainSelector k d Mtri hd (max (1/2) (cycleThreshold 3)) α pstar (ρ₀/16)
        βP ηP ηH βH c B εTri ε χtri (2*(3*d)) hp ∧
      OrdinaryReferenceCutsDomainSelector d Mcut hd α pstar (ρ₀/16) δ h ε χcut (2*(3*d))
end Oberwolfach
