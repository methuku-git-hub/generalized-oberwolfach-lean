module

public import Oberwolfach.OrdinaryReferenceCutsDomainSelector

@[expose] public section
/-! Select a reusable fixed-domain joint rim and spoke cut callback. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reference_cuts_domain_selector_choice
    (α pstar ω:ℝ) (hα:0<α) (hα1:α≤1/2) (hp:0<pstar) (hp1:pstar≤1) (hω:0<ω):
    ∃δ h:ℝ,0<δ ∧ δ<1/4 ∧ 0<h ∧ ∀(η χ Lconf:ℝ),0<η→η<1→0<χ→0≤Lconf→
    ∀d:ℕ,∀hd:2≤d,∃M:ℕ,1≤M ∧ OrdinaryReferenceCutsDomainSelector d M hd α pstar ω δ h η χ Lconf :=by
  obtain ⟨δ,h,hδ,hδ1,hh,hmain⟩:=ordinary_reference_cuts_fixed_domains α pstar ω hα hα1 hp hp1 hω
  refine ⟨δ,h,hδ,hδ1,hh,?_⟩
  intro η χ Lconf hη hη1 hχ hL d hd
  obtain ⟨M,hM,hselector⟩:=hmain η χ Lconf hη hη1 hχ hL d hd
  exact ⟨M,hM,hselector⟩
end Oberwolfach
