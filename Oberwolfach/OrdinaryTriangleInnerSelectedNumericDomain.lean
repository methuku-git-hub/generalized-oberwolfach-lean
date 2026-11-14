module

public import Oberwolfach.OrdinaryTriangleRootFreeCoherentEarlyChoicesWithDomain

@[expose] public section
/-! Name the inner numerical data chosen before the failure allowance.
The selected cap can later be shared with the parent event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach

def OrdinaryTriangleInnerSelectedNumericDomain
    (α c C ε ρ₀ pmin ηHub eParent hParent κe ηend εf εrows othercap:ℝ)
    (ξ Kdom Bweight tHub eEvent hEvent capHub γold κold δ tpot lamInner bold Bold βcap:ℝ):Prop :=
    0<ξ ∧ ξ<ηHub ∧ 0<Kdom ∧ 0<Bweight ∧ 0<tHub ∧ 0<eEvent ∧ 0<hEvent ∧ 0<capHub ∧
    eEvent≤eParent ∧ hEvent≤hParent ∧
    1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom ∧
    OrdinaryTriangleInnerEndpointAfterSetup α c C ε ρ₀ pmin ξ c Bweight ηHub Kdom eParent hParent capHub ∧
    OrdinaryDeepNumericParameters pmin κe (1/Kdom) ηend εf (2*Kdom)
      γold κold δ εrows tpot lamInner bold Bold ∧
    OrdinaryTriangleInnerNumericParameters pmin κe εf ηend εrows δ εrows tpot lamInner ∧
    0<βcap ∧ βcap≤othercap ∧ ∀β:ℝ,0≤β→β≤βcap→
      β≤1/4 ∧ β≤α/8 ∧ ξ+2*β<ηHub ∧ β≤2*δ*κe*pmin

theorem ordinary_triangle_inner_selected_numeric_domain
    (α c C ε ρ₀ pmin ηHub eParent hParent κe ηend εf εrows othercap:ℝ)
    (h:OrdinaryTriangleEndpointNumericDomainExists α c C ε ρ₀ pmin ηHub eParent hParent κe ηend εf εrows othercap):
    ∃ξ Kdom Bweight tHub eEvent hEvent capHub γold κold δ tpot lamInner bold Bold βcap:ℝ,
      OrdinaryTriangleInnerSelectedNumericDomain α c C ε ρ₀ pmin ηHub eParent hParent κe ηend εf εrows othercap
        ξ Kdom Bweight tHub eEvent hEvent capHub γold κold δ tpot lamInner bold Bold βcap :=by
  obtain ⟨ξ,Kdom,Bweight,tHub,eEvent,hEvent,capHub,hξ,hξη,hK,hB,ht,he,hh,hcap,heP,hhP,hKdom,hsetup,
    γold,κold,δ,tpot,lamInner,bold,Bold,βcap,hdeep,hinner,hβcap,hother,hβ⟩:=h
  exact ⟨ξ,Kdom,Bweight,tHub,eEvent,hEvent,capHub,γold,κold,δ,tpot,lamInner,bold,Bold,βcap,
    hξ,hξη,hK,hB,ht,he,hh,hcap,heP,hhP,hKdom,hsetup,hdeep,hinner,hβcap,hother,hβ⟩
end Oberwolfach
