module

public import Oberwolfach.OrdinaryTriangleInnerEndpointPreselect

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_inner_endpoint_preselect_with_domain
    (α c C ε ρ₀ pmin ηHub eParent hParent:ℝ)
    (hselector:OrdinaryNamedTriangleInnerEndpointSelector α c C)
    (hc:0<c) (hC:0<C) (hε:0<ε) (hε1:ε<1/4) (hρ:0<ρ₀)
    (hp:0<pmin) (hp1:pmin≤1) (hη:0<ηHub) (he:0<eParent) (hh:0<hParent):
    ∃ξ Kdom Bweight t eEvent hEvent cap:ℝ,
      0<ξ ∧ ξ<ηHub ∧ 0<Kdom ∧ 0<Bweight ∧ 0<t ∧ 0<eEvent ∧ 0<hEvent ∧ 0<cap ∧
      eEvent≤eParent ∧ hEvent≤hParent ∧
      1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom ∧
      OrdinaryTriangleInnerEndpointAfterSetup α c C ε ρ₀ pmin ξ c Bweight ηHub Kdom eParent hParent cap :=by
  let ξ:=ηHub/4
  let Kdom:=1+1/(ε/2)+1/((ε/2)*(ρ₀/8))+2/ε
  let Bweight:ℝ:=(4*C/pmin^7)*Kdom^2
  have hξ:0<ξ:=by dsimp [ξ];positivity
  have hξcap:ξ<ηHub:=by dsimp [ξ];linarith
  have hK:0<Kdom:=by dsimp [Kdom];positivity
  have hB:0<Bweight:=by dsimp [Bweight];positivity
  have hA:0≤1/(ε/2):=by positivity
  have hB':0≤1/((ε/2)*(ρ₀/8)):=by positivity
  have hC':0≤2/ε:=by positivity
  have hK1:2/ε≤Kdom:=by dsimp [Kdom];linarith
  have hK2:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom:=by dsimp [Kdom];linarith
  obtain ⟨t,eEvent,hEvent,cap,ht,hevent,hhevent,hcap,hebound,hhbound,hafter⟩:=
    hselector ε ρ₀ pmin ξ c Bweight ηHub Kdom eParent hParent hε hε1 hρ hp hp1 hξ hK1 hK2
      (le_refl _) (by dsimp [Bweight];exact le_rfl) he hh
  exact ⟨ξ,Kdom,Bweight,t,eEvent,hEvent,cap,hξ,hξcap,hK,hB,ht,hevent,hhevent,hcap,hebound,hhbound,hK2,hafter⟩
end Oberwolfach
