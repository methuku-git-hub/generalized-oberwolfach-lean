module

public import Oberwolfach.OrdinaryGeneralReferenceEventHierarchy
public import Oberwolfach.OrdinaryGeneralDeepSafeCapacityRuleLinear

@[expose] public section
/-! Choose the general-wheel common event and the root packing error before
    selecting pairing tolerances, on the original host parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
set_option maxRecDepth 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_deep_reference_capacity_hierarchy_linear_min
    (kmin m d:ℕ) (hm:3≤m) (hd:2≤d) (α ρ₀ pstar ηP:ℝ) (hα:0<α) (hα1:α≤1/2)
    (hθ1:max (1/2) (cycleThreshold (m+1))+α/2≤1)
    (hρ₀:0<ρ₀) (hp:0<pstar) (hp1:pstar≤1) (hηP:0<ηP):
    ∃(δ h βP row:ℝ) (k:ℕ) (βH c B εstar cLinear:ℝ),
      0<δ ∧ δ<1/4 ∧ 0<h ∧ 0<βP ∧ 0<row ∧ m+3≤k ∧ kmin≤k ∧
      0<βH ∧ 0<c ∧ 0<B ∧ 0<εstar ∧ 0<cLinear ∧
      OrdinaryGeneralDeepSafeCapacityRuleLinear m k hm α (ρ₀/16) (βH/8)
        (c*(1-δ)^((m+1)-1)) (B/((ρ₀/16)*pstar^(2*(m+1)-1))) (h/2) (δ/2) εstar cLinear ∧
    ∀(ηH ε χhost χcut:ℝ),0<ηH→0<ε→ε<1→0<χhost→0<χcut→
    ∃εTri βmax:ℝ,0<εTri ∧ 0<βmax ∧ βmax≤1/4 ∧ βmax≤α/4 ∧ βmax≤εTri ∧
    ∃Mhost Mcut:ℕ,1≤Mhost ∧ 1≤Mcut ∧
      OrdinaryGeneralFixedDomainSelector m k d Mhost hm hd (max (1/2) (cycleThreshold (m+1))) α pstar (ρ₀/16)
        βP ηP row ηH βH c B εTri ε χhost (2*(3*d)) hp ∧
      OrdinaryReferenceCutsDomainSelector d Mcut hd α pstar (ρ₀/16) δ h ε χcut (2*(3*d)) :=by
  obtain ⟨N,hcap⟩:=ordinary_general_deep_safe_capacity_rule_choice_linear m hm α hα
  obtain ⟨δ,h,βP,row,k,βH,c,B,hδ,hδ1,hh,hβP,hrow,hk,hkN,hβH,hc,hB,hevents⟩:=
    ordinary_general_reference_event_hierarchy (max N kmin) m d hm hd α ρ₀ pstar ηP hα hα1 hθ1 hρ₀ hp hp1 hηP
  have hkN':N≤k:=le_trans (le_max_left _ _) hkN
  have hkmin:kmin≤k:=le_trans (le_max_right _ _) hkN
  have hlower:0<c*(1-δ)^((m+1)-1):=by
    exact mul_pos hc (pow_pos (by linarith) _)
  have hupper:0<B/((ρ₀/16)*pstar^(2*(m+1)-1)):=by positivity
  obtain ⟨εstar,cLinear,hεstar,hcLinear,hrule⟩:=hcap k hkN' (ρ₀/16) (βH/8) (c*(1-δ)^((m+1)-1))
    (B/((ρ₀/16)*pstar^(2*(m+1)-1))) (h/2) (δ/2)
    (by positivity) (by positivity) hlower hupper (by positivity) (by positivity) (by linarith)
  exact ⟨δ,h,βP,row,k,βH,c,B,εstar,cLinear,hδ,hδ1,hh,hβP,hrow,hk,hkmin,hβH,hc,hB,hεstar,hcLinear,hrule,hevents⟩
end Oberwolfach
