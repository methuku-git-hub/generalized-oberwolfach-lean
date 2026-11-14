module

public import Oberwolfach.OrdinaryTriangleInnerBoundaryChoice
public import Oberwolfach.OrdinaryTriangleInnerNumericHierarchy
public import Oberwolfach.OrdinaryTriangleInnerTerminalThreshold

@[expose] public section
/-! Fix the inner-parent, vortex, root and cleanup boundary constants in a
noncircular order, before choosing the sample and the host size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach

structure OrdinaryTriangleInnerFullNumericSelection
    (root edit cBoundary εcap γ ζ pmin κe εfactor ηend εrows:ℝ)
    (δ εcount t lam lamRoot εv βe βh θ:ℝ):Prop where
  parent:OrdinaryTriangleInnerNumericParameters pmin κe εfactor ηend εrows δ εcount t lam
  vortex_pos:0<εv
  vortex_cap:εv≤εcap
  vortex_small:εv<1/4
  root_eq:lamRoot=2*εv^2
  root_pos:0<lamRoot
  root_cap:lamRoot≤root
  root_quarter:lamRoot≤1/4
  betaE_pos:0<βe
  betaH_pos:0<βh
  profileE:2*βe≤cBoundary*εv
  profileH:2*βh≤cBoundary*εv
  root_edge:lamRoot≤βe/4
  root_hub:lamRoot≤βh/2
  root_edit:3*lamRoot≤edit/4
  root_level:lamRoot*3≤edit/4
  matching_pos:0<θ
  matching_factor:θ≤ζ*(γ/4)*εv
  matching_edge:θ≤βe
  matching_hub:θ≤βh
  terminal:∀N₀ b₀:ℕ,∃M:ℕ,N₀≤M ∧ 32≤M ∧ 4/εv≤(M:ℝ) ∧ (b₀:ℝ)≤lam*M
  sample:∀pcap othercap:ℝ,0<pcap→0<othercap→
    ∃ellCap pbound:ℝ,ellCap=θ/64 ∧ 0<ellCap ∧ ellCap≤βe/8 ∧ ellCap≤βh/4 ∧
      0<pbound ∧ pbound≤pcap ∧
    ∀p:ℝ,0<p→p≤pbound→∃εsup cap δsample loadCap:ℝ,
      p≤1 ∧ p≤4*θ ∧ 20*Real.sqrt (2*p)≤θ/2 ∧
      0<εsup ∧ εsup≤p^2/4 ∧ 0<cap ∧ cap≤othercap ∧ cap≤βe/8 ∧ cap≤βh/4 ∧
      0<δsample ∧ 0<loadCap ∧ loadCap≤1 ∧
      βe+3*max cap ellCap≤2*βe ∧ βh+2*ellCap≤2*βh ∧
      (∀load ξ:ℝ,0≤load→load≤loadCap→0≤ξ→ξ≤load^2/160→
        max (18*load+3*lamRoot) ((3*load+lamRoot)*3)≤ellCap ∧ 10*ξ≤cap) ∧
      (∀τ ν η ell:ℝ,0≤τ→0≤ν→0≤η→0≤ell→τ≤cap→ν≤cap→η≤cap→ell≤ellCap→
        τ+ν≤p^2/4 ∧ τ+ν+(p*ell+δsample)≤θ*p/4 ∧ ν+η≤θ*p/4) ∧
      ∃N:ℕ,∀n:ℕ,N≤n→2≤θ*p*n/4

theorem ordinary_triangle_inner_full_numeric_selector
    (root edit cBoundary εcap γ ζ pmin κe εfactor ηend εrows:ℝ)
    (hroot:0<root) (hedit:0<edit) (hc:0<cBoundary) (hεcap:0<εcap)
    (hγ:0<γ) (hζ:0<ζ) (hp:0<pmin) (hκ:0<κe) (hεf:0<εfactor) (hη:0<ηend) (hrows:0<εrows):
    ∃δ εcount t lam lamRoot εv βe βh θ:ℝ,
      OrdinaryTriangleInnerFullNumericSelection root edit cBoundary εcap γ ζ pmin κe εfactor ηend εrows
        δ εcount t lam lamRoot εv βe βh θ:=by
  obtain ⟨δ,εcount,t,lam,hnum⟩:=ordinary_triangle_inner_numeric_hierarchy pmin κe εfactor ηend εrows
    hp hκ hεf hη hrows
  let c:ℝ:=min cBoundary 1/4
  have hc':0<c:=by dsimp [c];positivity
  have hcCap:2*c≤cBoundary:=by
    have hh:=min_le_left cBoundary (1:ℝ)
    dsimp [c];linarith
  obtain ⟨lamRoot,εv,βe,βh,θ,hεv,hεcap,hεsmall,hrootEq,hrootPos,hrootCap,hrootQuarter,
    hβeEq,hβhEq,hβe,hβh,hrootE,hrootH,hrootEdit,hrootLevel,hθ,hθfactor,hθE,hθH,hsample⟩:=
      ordinary_triangle_inner_boundary_choice root edit c c εcap γ ζ hroot hedit hc' hc' hεcap hγ hζ
  have hprofileE:2*βe≤cBoundary*εv:=by
    rw [hβeEq]
    have hh:=mul_le_mul_of_nonneg_right hcCap hεv.le
    nlinarith only [hh]
  have hprofileH:2*βh≤cBoundary*εv:=by
    rw [hβhEq]
    have hh:=mul_le_mul_of_nonneg_right hcCap hεv.le
    nlinarith only [hh]
  refine ⟨δ,εcount,t,lam,lamRoot,εv,βe,βh,θ,⟨hnum,hεv,hεcap,hεsmall,hrootEq,hrootPos,hrootCap,hrootQuarter,
    hβe,hβh,hprofileE,hprofileH,hrootE,hrootH,hrootEdit,hrootLevel,hθ,hθfactor,hθE,hθH,?_,hsample⟩⟩
  intro N₀ b₀
  exact ordinary_triangle_inner_terminal_threshold εv lam hεv hnum.lambda_pos b₀ N₀
end Oberwolfach
