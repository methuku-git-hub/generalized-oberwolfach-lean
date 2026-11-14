module

public import Oberwolfach.OrdinaryDeepCapBeforeLoadChoice
public import Oberwolfach.OrdinarySelectedCostRateBeforeSpacing

@[expose] public section
/-! Fix the deep event cap and its selected-cost rate before the matching
spacing, certificate load and all failure allowances. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_cap_cost_before_spacing
    (m K:ℕ) (α ρ₀ pmin αcut c C a ε₀ ρ θdeep:ℝ)
    (hdeep:OrdinaryDeepRowsCutsEarlyBeforeLoad m K α ρ₀ pmin αcut c C a ε₀ ρ θdeep)
    (ε ξ b Bweight ηHub Kdom eParent hParent:ℝ)
    (hε:0<ε) (hε1:ε<1/4) (hεa:ε≤a) (hερ:ε≤ρ₀/16) (hρ:0<ρ₀)
    (hξ:0<ξ) (hK:2/ε≤Kdom) (hKdom:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom) (hb:b≤c)
    (hB:(4*C/pmin^(3*m+1))*Kdom^m≤Bweight) (he:0<eParent) (hh:0<hParent):
    ∃t eEvent hEvent cap costRate:ℝ,0<t ∧ 0<eEvent ∧ 0<hEvent ∧ 0<cap ∧
      eEvent≤eParent ∧ hEvent≤hParent ∧ 0<costRate ∧ (∀d:ℕ,OrdinarySelectedCostRate ε ρ₀ cap d costRate) ∧
      ∀(aLoad εR εH:ℝ),0<aLoad→aLoad≤a→0<εR→0<εH→
      ∀χinner χdeep χone χtwo χcut:ℝ,0<χinner→0<χdeep→0<χone→0<χtwo→0<χcut→
        OrdinaryDeepRowsCutsAfterParameters m K α ρ₀ pmin αcut c C a ε₀ ρ θdeep
          aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap :=by
  obtain ⟨t,eEvent,hEvent,cap,ht,hevent,hhevent,hcap,hebound,hhbound,hselect⟩:=
    ordinary_deep_cap_before_load_choice m K α ρ₀ pmin αcut c C a ε₀ ρ θdeep hdeep
      ε ξ b Bweight ηHub Kdom eParent hParent hε hε1 hεa hερ hξ hK hKdom hb hB he hh
  obtain ⟨costRate,hcost,hcostall⟩:=ordinary_selected_cost_rate_before_spacing ε ρ₀ cap hε hε1 hρ hcap
  exact ⟨t,eEvent,hEvent,cap,costRate,ht,hevent,hhevent,hcap,hebound,hhbound,hcost,hcostall,hselect⟩
end Oberwolfach
