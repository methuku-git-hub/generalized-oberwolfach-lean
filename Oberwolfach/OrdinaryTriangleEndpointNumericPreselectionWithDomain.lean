module

public import Oberwolfach.OrdinaryTriangleInnerParentNumericSpacing
public import Oberwolfach.OrdinaryTriangleInnerEndpointPreselectWithDomain

@[expose] public section
/-! Select the inner/endpoint event cap, exact numerical hierarchy and
vortex spacing before the failure allowance and conflict bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_endpoint_numeric_preselection_with_domain
    (α c C ε ρ₀ pmin ηHub eParent hParent κe ηend εf εrows othercap:ℝ)
    (hselector:OrdinaryNamedTriangleInnerEndpointSelector α c C)
    (hα:0<α) (hc:0<c) (hC:0<C) (hε:0<ε) (hε1:ε<1/4) (hρ:0<ρ₀)
    (hp:0<pmin) (hp1:pmin≤1) (hHub:0<ηHub) (he:0<eParent) (hh:0<hParent)
    (hκ:0<κe) (hη:0<ηend) (hεf:0<εf) (hrows:0<εrows)
    (hrowsGeom:εrows≤min (pmin^4/16) (pmin^3/2)) (hother:0<othercap):
    ∃ξ Kdom Bweight tHub eEvent hEvent capHub:ℝ,
      0<ξ ∧ ξ<ηHub ∧ 0<Kdom ∧ 0<Bweight ∧ 0<tHub ∧ 0<eEvent ∧ 0<hEvent ∧ 0<capHub ∧
      eEvent≤eParent ∧ hEvent≤hParent ∧
      1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom ∧
      OrdinaryTriangleInnerEndpointAfterSetup α c C ε ρ₀ pmin ξ c Bweight ηHub Kdom eParent hParent capHub ∧
    ∃γold κold δ tpot lamInner bold Bold βcap:ℝ,
      OrdinaryDeepNumericParameters pmin κe (1/Kdom) ηend εf (2*Kdom)
        γold κold δ εrows tpot lamInner bold Bold ∧
      OrdinaryTriangleInnerNumericParameters pmin κe εf ηend εrows δ εrows tpot lamInner ∧
      0<βcap ∧ βcap≤othercap ∧ ∀β:ℝ,0≤β→β≤βcap→
        β≤1/4 ∧ β≤α/8 ∧ ξ+2*β<ηHub ∧ β≤2*δ*κe*pmin :=by
  obtain ⟨ξ,Kdom,Bweight,tHub,eEvent,hEvent,capHub,hξ,hξcap,hK,hB,ht,hevent,hhevent,hcap,hebound,hhbound,hKdom,hsetup⟩:=
    ordinary_triangle_inner_endpoint_preselect_with_domain α c C ε ρ₀ pmin ηHub eParent hParent
      hselector hc hC hε hε1 hρ hp hp1 hHub he hh
  obtain ⟨γold,κold,δ,tpot,lamInner,bold,Bold,βcap,hdeep,hinner,hβ,hβcap,hspacing⟩:=
    ordinary_triangle_inner_parent_numeric_spacing α ξ ηHub pmin κe ηend εf Kdom εrows othercap
      hα hξ.le hξcap hp hκ hη hεf hK hrows hrowsGeom hother
  exact ⟨ξ,Kdom,Bweight,tHub,eEvent,hEvent,capHub,hξ,hξcap,hK,hB,ht,hevent,hhevent,hcap,hebound,hhbound,hKdom,hsetup,
    γold,κold,δ,tpot,lamInner,bold,Bold,βcap,hdeep,hinner,hβ,hβcap,hspacing⟩
end Oberwolfach
