module

public import Oberwolfach.OrdinaryDeepFifteenQuarticGeometryCoverScaleChoice
public import Oberwolfach.OrdinaryDeepTraceCoverAndSeparatedBalanceExplicitDecay

@[expose] public section
/-! Choose linear boundary rates, a vortex scale, a quadratic cover load and
compatible later cover/balance callbacks in one pre-host hierarchy. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_deep_fifteen_quartic_pre_host_scale_and_selected_balance_decay
    (mWheel d:ℕ) (hm:3≤mWheel)
    (ρ₀ hmin href δlimit a ρ θ α pmin pCap νCap cap₀ cLinear cGeom ξGeom:ℝ)
    (hρ₀:0<ρ₀) (hhmin:0<hmin) (hhref:0<href) (hδlimit:0<δlimit)
    (ha:0<a) (hρ:0<ρ) (hθ:0<θ) (hα:0<α) (hpmin:0<pmin)
    (hpCap:0<pCap) (hνCap:0<νCap) (hcap:0<cap₀) (hLinear:0<cLinear) (hGeom:0<cGeom) (hξ:0<ξGeom):
    ∃δcut ζcut εcut ζlimit εsample cBoundary pCoeff νCoeff εcap cLoad cEta:ℝ,
      0<δcut ∧ δcut<1/4 ∧ δcut≤δlimit ∧ 0<ζcut ∧ 0<εcut ∧ 0<ζlimit ∧ 0<εsample ∧
      0<cBoundary ∧ 0<pCoeff ∧ pCoeff≤pCap ∧ 512*pCoeff*((mWheel:ℝ)+1)<(cBoundary/2)^2 ∧
      0<νCoeff ∧ νCoeff≤νCap ∧ νCoeff≤pCoeff^2/64 ∧
      0<εcap ∧ εcap≤1 ∧ 0<cLoad ∧ cLoad≤1 ∧ 0<cEta ∧
    ∀ε:ℝ,0<ε→ε≤εcap→
    let βe:=cBoundary*ε/2;let βh:=cBoundary*ε/2;let ν:=νCoeff*ε^4;let p:=pCoeff*ε^2;let cap:=cap₀*ε^14;
    0<βe ∧ βe≤cBoundary*ε ∧ 0<βh ∧ βh≤cBoundary*ε ∧ 0<ν ∧ 0<p ∧
    512*p*((mWheel:ℝ)+1)<βe^2 ∧ 0<cap ∧ ν+cap≤p^2/4 ∧
    ∀ηpack γ:ℝ,
      cLinear*ordinarySafeCleanupScale (mWheel+1) p βe βh ν cap≤ηpack→
      cGeom*min 1 ηpack≤γ→
    ∃lam aLoad ξroot ηcover:ℝ,
      cap≤1 ∧ 0≤lam ∧ lam≤1/4 ∧ lam≤(ρ₀/8)/2 ∧ lam≤γ/(1000*((mWheel:ℝ)+2)) ∧
      ε≤ξGeom/2 ∧ ε≤ξGeom*(ρ₀/8)/2 ∧ 2*ε^15≤lam ∧
      aLoad=cLoad*ε^14 ∧ 0<aLoad ∧ aLoad≤1 ∧ aLoad≤γ/(1000*((mWheel:ℝ)+2)) ∧
      ξroot=min (ε/200) (aLoad^2/160) ∧ 0<ξroot ∧
      ηcover=δcut*(ρ₀/8)*ξroot/1000 ∧ cEta*ε^28≤ηcover ∧
    ∃ηbal:ℝ,0<ηbal ∧ ηbal≤ηcover ∧ ηbal*ε≤γ/8 ∧ ∀rateParent:ℝ,0<rateParent→
    ∃ζ δ rate:ℝ,0<ζ ∧ ζ≤ζlimit ∧ ζ≤rateParent ∧ 0<δ ∧ δ≤α ∧ δ≤ηbal ∧ 0<rate ∧ rate≤δ*(ε/2)^15 ∧
    ∀β:ℝ,0≤β→β≤1/4→β≤δ→∀C:ℝ,0≤C→
    ∃mBalance mCover:ℕ,1≤mBalance ∧ 1≤mCover ∧
      OrdinaryDeepTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηbal ζ cBoundary δ rate d 15 β C mBalance ∧
      OrdinaryDeepTraceCoverAt mWheel 0 15 ρ₀ hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ β ηbal d mCover :=by
  obtain ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,cBoundary,hδcut,hδcut1,hδlimit',hζcut,hεcut,hζlimit,hεsample,hεvortex,hεvortex1,hcBoundary,hcover⟩:=
    ordinary_deep_trace_cover_and_separated_balance_explicit_decay mWheel 0 15 hm (by omega) ρ₀ hmin href δlimit a ρ θ α pmin d
      hρ₀ hhmin hhref hδlimit ha hρ hθ hα hpmin
  let pCoeff:ℝ:=min (pCap/2) (cBoundary^2/(4096*((mWheel:ℝ)+1)))
  have hpCoeff:0<pCoeff:=by dsimp [pCoeff];positivity
  have hpCoeffCap:pCoeff≤pCap:=by
    have hh:=min_le_left (pCap/2) (cBoundary^2/(4096*((mWheel:ℝ)+1)))
    dsimp [pCoeff];linarith
  have hpCoeffBound:512*pCoeff*((mWheel:ℝ)+1)<(cBoundary/2)^2:=by
    have hh:=min_le_right (pCap/2) (cBoundary^2/(4096*((mWheel:ℝ)+1)))
    have hk:0<4096*((mWheel:ℝ)+1):=by positivity
    have hh':pCoeff*(4096*((mWheel:ℝ)+1))≤cBoundary^2:=(le_div_iff₀ hk).mp hh
    have hc2:0<cBoundary^2:=sq_pos_of_pos hcBoundary
    nlinarith only [hh',hc2]
  let νCoeff:ℝ:=min (νCap/2) (pCoeff^2/64)
  have hνCoeff:0<νCoeff:=by dsimp [νCoeff];positivity
  have hνCap':νCoeff≤νCap:=by have hh:=min_le_left (νCap/2) (pCoeff^2/64);dsimp [νCoeff];linarith
  have hνSq:νCoeff≤pCoeff^2/64:=min_le_right _ _
  obtain ⟨eGeom,cLoad,cEta,heGeom,heGeom1,hcLoad,hcLoad1,hcEta,hscale⟩:=
    ordinary_deep_fifteen_quartic_geometry_cover_scale_choice (mWheel+1) mWheel pCoeff (cBoundary/2) (cBoundary/2) νCoeff cap₀ cLinear cGeom ξGeom ρ₀ δcut
      hpCoeff (by positivity) (by positivity) hνCoeff hcap hLinear hGeom hξ hρ₀ hδcut
  let εcap:ℝ:=min eGeom (min εvortex (pCoeff^2/(64*(cap₀+1))))
  have hεcap:0<εcap:=by dsimp [εcap];positivity
  have hεcap1:εcap≤1:=(min_le_left _ _).trans heGeom1
  refine ⟨δcut,ζcut,εcut,ζlimit,εsample,cBoundary,pCoeff,νCoeff,εcap,cLoad,cEta,hδcut,hδcut1,hδlimit',hζcut,hεcut,hζlimit,hεsample,
    hcBoundary,hpCoeff,hpCoeffCap,hpCoeffBound,hνCoeff,hνCap',hνSq,hεcap,hεcap1,hcLoad,hcLoad1,hcEta,?_⟩
  intro ε hε he βe βh ν p cap
  have heGeom':ε≤eGeom:=he.trans (min_le_left _ _)
  have heVortex:ε≤εvortex:=he.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heScale:ε≤pCoeff^2/(64*(cap₀+1)):=he.trans ((min_le_right _ _).trans (min_le_right _ _))
  have heOne:ε≤1:=he.trans hεcap1
  have he10:ε^10≤ε:=by
    have hh:=mul_le_mul_of_nonneg_right (show ε^9≤1 from pow_le_one₀ hε.le heOne) hε.le
    nlinarith only [hh]
  have hcoef:cap₀*ε≤pCoeff^2/64:=by
    have hh:ε*(64*(cap₀+1))≤pCoeff^2:=(le_div_iff₀ (by positivity:0<64*(cap₀+1))).mp heScale
    nlinarith only [hh,hε]
  have hcapP:cap≤p^2/64:=by
    have hh:=mul_le_mul_of_nonneg_left he10 hcap.le
    have hh':=mul_le_mul_of_nonneg_right (show cap₀*ε^10≤pCoeff^2/64 by linarith only [hh,hcoef]) (show 0≤ε^4 by positivity)
    dsimp [cap,p]
    nlinarith only [hh']
  have hνP:ν≤p^2/64:=by
    have hh:=mul_le_mul_of_nonneg_right hνSq (show 0≤ε^4 by positivity)
    dsimp [ν,p]
    nlinarith only [hh]
  have hβe:0<βe:=by dsimp [βe];positivity
  have hβh:0<βh:=by dsimp [βh];positivity
  have hβebound:βe≤cBoundary*ε:=by dsimp [βe];nlinarith [mul_pos hcBoundary hε]
  have hβhbound:βh≤cBoundary*ε:=by dsimp [βh];nlinarith [mul_pos hcBoundary hε]
  have hν':0<ν:=by dsimp [ν];positivity
  have hp':0<p:=by dsimp [p];positivity
  have hprate:512*p*((mWheel:ℝ)+1)<βe^2:=by
    have hh:=mul_lt_mul_of_pos_right hpCoeffBound (sq_pos_of_pos hε)
    dsimp [p,βe]
    nlinarith only [hh]
  have hcap':0<cap:=by dsimp [cap];positivity
  refine ⟨hβe,hβebound,hβh,hβhbound,hν',hp',hprate,hcap',by nlinarith only [hcapP,hνP],?_⟩
  intro ηpack γ hpack hγ
  have hpack':cLinear*ordinarySafeCleanupScale (mWheel+1) (pCoeff*ε^2) ((cBoundary/2)*ε) ((cBoundary/2)*ε) (νCoeff*ε^4) (cap₀*ε^14)≤ηpack:=by
    convert hpack using 1 <;> dsimp [βe,βh,ν,p,cap] <;> ring
  obtain ⟨lam,aLoad,ξroot,ηcover,hcap1,hlam,hlam1,hlamρ,hlamγ,hεξ,hερ,hεroot,haEq,ha0,ha1,haγ,hξEq,hξ0,hηEq,hηlower⟩:=
    hscale ε hε heGeom' ηpack γ hpack' hγ
  obtain ⟨ξ',η',hξ',hη',hξ'0,hη'0,hcallbacks⟩:=hcover ε hε heVortex aLoad ha0 ha1
  have hξid:ξ'=ξroot:=hξ'.trans hξEq.symm
  have hηid:η'=ηcover:=by rw [hη',hξid,hηEq]
  rw [hξid,hηid] at hcallbacks
  refine ⟨lam,aLoad,ξroot,ηcover,hcap1,hlam,hlam1,hlamρ,hlamγ,hεξ,hερ,hεroot,haEq,ha0,ha1,haγ,hξEq,hξ0,hηEq,hηlower,?_⟩
  have hηcover:0<ηcover:=lt_of_lt_of_le (by positivity : 0<cEta*ε^28) hηlower
  have hK:0<(1000*((mWheel:ℝ)+2)):=by positivity
  have hγpos:0<γ:=by
    have hh: aLoad*(1000*((mWheel:ℝ)+2))≤γ:=(le_div_iff₀ hK).mp haγ
    exact (mul_pos ha0 hK).trans_le hh
  let ηbal:ℝ:=min (ηcover/2) (γ/(16*ε))
  have hηbal:0<ηbal:=by dsimp [ηbal];positivity
  have hηcover':ηbal≤ηcover:=by
    have hh:=min_le_left (ηcover/2) (γ/(16*ε))
    dsimp [ηbal];linarith
  have hηsmall:ηbal*ε≤γ/8:=by
    have hh:=min_le_right (ηcover/2) (γ/(16*ε))
    dsimp [ηbal] at *
    have hx:=mul_le_mul_of_nonneg_right hh hε.le
    have heq:(γ/(16*ε))*ε=γ/16:=by field_simp
    rw [heq] at hx
    linarith
  exact ⟨ηbal,hηbal,hηcover',hηsmall,hcallbacks ηbal hηbal hηcover'⟩
end Oberwolfach
