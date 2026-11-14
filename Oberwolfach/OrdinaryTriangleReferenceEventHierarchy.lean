module

public import Oberwolfach.OrdinaryTriangleFixedDomainSelectorChoice
public import Oberwolfach.OrdinaryReferenceCutsDomainSelectorChoice
public import Oberwolfach.OrdinaryNondeeperTriangleToleranceChoice
public import Oberwolfach.OrdinaryTrianglePackingSelectedError

@[expose] public section
/-! Choose the full-parent triangle weights and joint reference cuts before
the host, retaining their callbacks for later sampling tolerances. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_reference_event_hierarchy
    (d:ℕ) (hd:2≤d) (α ρ₀ pstar ηP:ℝ) (hα:0<α) (hα1:α≤1/2)
    (hθ1:max (1/2) (cycleThreshold 3)+α/2≤1)
    (hρ₀:0<ρ₀) (hp:0<pstar) (hp1:pstar≤1) (hηP:0<ηP):
    ∃(δ h βP:ℝ) (k:ℕ) (βH c B:ℝ),0<δ ∧ δ<1/4 ∧ 0<h ∧ 0<βP ∧
      5≤k ∧ ordinaryTrianglePackingThreshold α hα≤k ∧ 0<βH ∧ 0<c ∧ 0<B ∧
    ∀(ηH ε χtri χcut:ℝ),0<ηH→0<ε→ε<1→0<χtri→0<χcut→
    ∃εTri βmax:ℝ,0<εTri ∧ 0<βmax ∧ βmax≤1/4 ∧ βmax≤α/4 ∧ βmax≤εTri ∧
    ∃Mtri Mcut:ℕ,1≤Mtri ∧ 1≤Mcut ∧
      OrdinaryTriangleFixedDomainSelector k d Mtri hd (max (1/2) (cycleThreshold 3)) α pstar (ρ₀/16)
        βP ηP ηH βH c B εTri ε χtri (2*(3*d)) hp ∧
      OrdinaryReferenceCutsDomainSelector d Mcut hd α pstar (ρ₀/16) δ h ε χcut (2*(3*d)) :=by
  obtain ⟨δ,h,hδ,hδ1,hh,hcut⟩:=ordinary_reference_cuts_domain_selector_choice α pstar (ρ₀/16)
    hα hα1 hp hp1 (by positivity)
  obtain ⟨βP,hβP,hβmax,hβhub,hβchoice⟩:=ordinary_nondeeper_triangle_tolerance_choice α pstar (ρ₀/16)
    hα hp (by positivity)
  obtain ⟨k,βH,c,B,hk,hkmin,hβH,hc,hB,htri⟩:=ordinary_triangle_fixed_domain_selector_choice
    (max 4 (ordinaryTrianglePackingThreshold α hα)) d hd (max (1/2) (cycleThreshold 3)) α pstar (ρ₀/16)
    βP ηP (2*(3*d)) (le_max_right _ _) hα (by linarith) hθ1 hp hp1 (by positivity)
    hβP hβmax hβhub hηP (by positivity)
  refine ⟨δ,h,βP,k,βH,c,B,hδ,hδ1,hh,hβP,hk,by omega,hβH,hc,hB,?_⟩
  intro ηH ε χtri χcut hηH hε hε1 hχtri hχcut
  obtain ⟨εTri,hεTri,Mtri,hMtri,htri⟩:=htri ηH ε χtri hηH hε hε1 hχtri
  obtain ⟨Mcut,hMcut,hcut⟩:=hcut ε χcut (2*(3*d)) hε hε1 hχcut (by positivity) d hd
  let βmax:=min (1/4:ℝ) (min (α/4) εTri)/2
  have hβ:0<βmax:=by dsimp [βmax];positivity
  have hβ1:βmax≤1/4:=by have hh:=min_le_left (1/4:ℝ) (min (α/4) εTri);dsimp [βmax];linarith
  have hβα:βmax≤α/4:=by have hh:=le_trans (min_le_right (1/4:ℝ) (min (α/4) εTri)) (min_le_left _ _);dsimp [βmax];linarith
  have hβε:βmax≤εTri:=by have hh:=le_trans (min_le_right (1/4:ℝ) (min (α/4) εTri)) (min_le_right _ _);dsimp [βmax];linarith
  exact ⟨εTri,βmax,hεTri,hβ,hβ1,hβα,hβε,Mtri,Mcut,hMtri,hMcut,htri,hcut⟩
end Oberwolfach
