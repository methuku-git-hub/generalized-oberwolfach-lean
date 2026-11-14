module

public import Oberwolfach.OrdinaryTriangleParentAfterFailureAllCapsWithBounds

@[expose] public section
/-! Add a positive spacing cap to the already selected parent and cut
callbacks without changing any reference parameter. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_parent_cap_from_selected_reference
    (k d:ℕ) (hd:2≤d) (α ρ₀ pmin βP ηP ηH βH cParent Bparent ε χhost δref href χref:ℝ)
    (hp:0<pmin) (hα:0<α)
    (hselected:∃εTri:ℝ,0<εTri ∧ ∃Mhost Mcut:ℕ,1≤Mhost ∧ 1≤Mcut ∧
      OrdinaryTriangleFixedDomainSelector k d Mhost hd (max (1/2) (cycleThreshold 3)) α pmin (ρ₀/16)
        βP ηP ηH βH cParent Bparent εTri ε χhost (2*(3*d)) hp ∧
      OrdinaryReferenceCutsDomainSelector d Mcut hd α pmin (ρ₀/16) δref href ε χref (2*(3*d))):
    ∃εTri βmax:ℝ,0<εTri ∧ 0<βmax ∧ βmax≤1/4 ∧ βmax≤α/4 ∧ βmax≤εTri ∧
      ∃Mhost Mcut:ℕ,1≤Mhost ∧ 1≤Mcut ∧
        OrdinaryTriangleFixedDomainSelector k d Mhost hd (max (1/2) (cycleThreshold 3)) α pmin (ρ₀/16)
          βP ηP ηH βH cParent Bparent εTri ε χhost (2*(3*d)) hp ∧
        OrdinaryReferenceCutsDomainSelector d Mcut hd α pmin (ρ₀/16) δref href ε χref (2*(3*d)) :=by
  obtain ⟨εTri,hεTri,Mhost,Mcut,hMhost,hMcut,hselector,hcuts⟩:=hselected
  let βmax:ℝ:=min (1/4:ℝ) (min (α/4) εTri)/2
  have hβ:0<βmax:=by dsimp [βmax];positivity
  have hβ1:βmax≤1/4:=by have hh:=min_le_left (1/4:ℝ) (min (α/4) εTri);dsimp [βmax];linarith
  have hβα:βmax≤α/4:=by have hh:=le_trans (min_le_right (1/4:ℝ) (min (α/4) εTri)) (min_le_left _ _);dsimp [βmax];linarith
  have hβε:βmax≤εTri:=by have hh:=le_trans (min_le_right (1/4:ℝ) (min (α/4) εTri)) (min_le_right _ _);dsimp [βmax];linarith
  exact ⟨εTri,βmax,hεTri,hβ,hβ1,hβα,hβε,Mhost,Mcut,hMhost,hMcut,hselector,hcuts⟩
end Oberwolfach
