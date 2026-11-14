module

public import Oberwolfach.OrdinaryTriangleInnerNumericHierarchy
public import Oberwolfach.OrdinaryTriangleInnerSampledScaleChoice
public import Oberwolfach.OrdinaryTriangleInnerTerminalThreshold

@[expose] public section
/-! Select the inner-domain error constants first, then the vortex and root
scale, then sampling and finite terminal thresholds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach

structure OrdinaryTriangleInnerOrderedRates
    (root edit eCoeff hCoeff εcap γ ζ pmin κe εfactor ηend εrows:ℝ)
    (δ εcount t lam lamRoot εv βe βh θ:ℝ):Prop where
  parent:OrdinaryTriangleInnerNumericParameters pmin κe εfactor ηend εrows δ εcount t lam
  vortex_pos:0<εv
  vortex_cap:εv≤εcap
  vortex_small:εv<1/4
  root_eq:lamRoot=2*εv^2
  root_pos:0<lamRoot
  root_cap:lamRoot≤root
  root_quarter:lamRoot≤1/4
  betaE_eq:βe=eCoeff*εv
  betaH_eq:βh=hCoeff*εv
  betaE_pos:0<βe
  betaH_pos:0<βh
  root_edge:lamRoot≤βe/4
  root_hub:lamRoot≤βh/2
  root_edit:3*lamRoot≤edit/4
  root_level:lamRoot*3≤edit/4
  matching_eq:θ=ζ*(γ/4)*εv
  matching_pos:0<θ
  terminal:∀N₀ b₀:ℕ,∃M:ℕ,N₀≤M ∧ 32≤M ∧ 4/εv≤(M:ℝ) ∧ (b₀:ℝ)≤lam*M
  sample:∀pcap othercap:ℝ,0<pcap→0<othercap→
    ∃ellCap pbound:ℝ,ellCap=θ/64 ∧ 0<ellCap ∧ 0<pbound ∧ pbound≤pcap ∧
    ∀p:ℝ,0<p→p≤pbound→∃εsup cap δsample loadCap:ℝ,
      p≤1 ∧ p≤4*θ ∧ 20*Real.sqrt (2*p)≤θ/2 ∧
      0<εsup ∧ εsup≤p^2/4 ∧ 0<cap ∧ cap≤othercap ∧ 0<δsample ∧ 0<loadCap ∧ loadCap≤1 ∧
      (∀load ξ:ℝ,0≤load→load≤loadCap→0≤ξ→ξ≤load^2/160→
        max (18*load+3*lamRoot) ((3*load+lamRoot)*3)≤ellCap ∧ 10*ξ≤cap) ∧
      (∀τ ν η ell:ℝ,0≤τ→0≤ν→0≤η→0≤ell→τ≤cap→ν≤cap→η≤cap→ell≤ellCap→
        τ+ν≤p^2/4 ∧ τ+ν+(p*ell+δsample)≤θ*p/4 ∧ ν+η≤θ*p/4) ∧
      ∃N:ℕ,∀n:ℕ,N≤n→2≤θ*p*n/4

theorem ordinary_triangle_inner_ordered_numeric_selector
    (root edit eCoeff hCoeff εcap γ ζ pmin κe εfactor ηend εrows:ℝ)
    (hroot:0<root) (hedit:0<edit) (he:0<eCoeff) (hh:0<hCoeff) (hεcap:0<εcap)
    (hγ:0<γ) (hζ:0<ζ) (hp:0<pmin) (hκ:0<κe) (hεf:0<εfactor) (hη:0<ηend) (hrows:0<εrows):
    ∃δ εcount t lam lamRoot εv βe βh θ:ℝ,
      OrdinaryTriangleInnerOrderedRates root edit eCoeff hCoeff εcap γ ζ pmin κe εfactor ηend εrows
        δ εcount t lam lamRoot εv βe βh θ:=by
  obtain ⟨δ,εcount,t,lam,hnum⟩:=ordinary_triangle_inner_numeric_hierarchy pmin κe εfactor ηend εrows
    hp hκ hεf hη hrows
  obtain ⟨lamRoot,εv,βe,βh,θ,hεv,hεcap,hεsmall,hrootEq,hrootPos,hrootCap,hrootQuarter,
    hβeEq,hβhEq,hβe,hβh,hrootE,hrootH,hrootEdit,hrootLevel,hθeq,hθ,hsample⟩:=
      ordinary_triangle_inner_sampled_scale_choice root edit eCoeff hCoeff εcap γ ζ hroot hedit he hh hεcap hγ hζ
  refine ⟨δ,εcount,t,lam,lamRoot,εv,βe,βh,θ,⟨hnum,hεv,hεcap,hεsmall,hrootEq,hrootPos,hrootCap,hrootQuarter,
    hβeEq,hβhEq,hβe,hβh,hrootE,hrootH,hrootEdit,hrootLevel,hθeq,hθ,?_,hsample⟩⟩
  intro N₀ b₀
  exact ordinary_triangle_inner_terminal_threshold εv lam hεv hnum.lambda_pos b₀ N₀
end Oberwolfach
