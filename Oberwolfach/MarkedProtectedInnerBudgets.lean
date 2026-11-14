module

public import Oberwolfach.MarkedProtectedLocalScale

@[expose] public section

/-! Numerical inputs for the actual inner profiles, including the change
2 times the number of removed hubs divided by rho in the degree target. -/
set_option autoImplicit false
set_option maxHeartbeats 14000000
namespace Oberwolfach

theorem marked_protected_inner_budget_scale
    (r K h:ℕ) (omega kappa rho t zeta epsilon etaEnd a theta etaEmax:ℝ)
    (ho:0<omega) (hk:0<kappa) (hrho:0<rho) (ht:0<t) (hz:0<zeta)
    (he:0<epsilon) (hEnd:0<etaEnd) (ha:0<a) (hth:0<theta) (hmax:0<etaEmax):
    ∃ delta:ℝ,0<delta∧∀ x:ℝ,0≤x→x≤delta→
    (4*K+3*r+50:ℝ)*x≤kappa/2∧24*x≤zeta*(omega/2)∧3*(r+5:ℝ)*x≤zeta*(omega/2)∧
    (1+h*(24+3*(r+5:ℝ)))*x≤epsilon*(omega/2)∧
    2*(1+h*(24+3*(r+5:ℝ)))*x≤etaEnd*a/2∧
    (3+2/rho+h*(24+3*(r+5:ℝ)))*x≤t*omega/16∧
    8*x≤theta∧(r+6:ℝ)*x≤theta/8∧(r+6:ℝ)*(96+3*(r+5:ℝ))*x≤theta/4∧
    x≤etaEmax∧x≤omega/4∧x≤kappa:=by
  obtain ⟨delta,hd,hall⟩:=marked_protected_local_scale_exists r K h (omega/2) kappa t zeta epsilon
    etaEnd a theta etaEmax (by positivity) hk ht hz he hEnd ha hth hmax
  obtain ⟨b,hb,hbB⟩:=exists_pos_mul_lt (show 0<t*omega/16 by positivity)
    (3+2/rho+h*(24+3*(r+5:ℝ)))
  refine ⟨min delta b,lt_min hd hb,?_⟩
  intro x hx hxd
  obtain ⟨h0,h1,h2,h3,h4,_,h6,h7,h8,h9,h10,h11⟩:=hall x hx (hxd.trans (min_le_left _ _))
  have hC:0≤(3+2/rho+h*(24+3*(r+5:ℝ))):=by positivity
  have hxB:=mul_le_mul_of_nonneg_left (hxd.trans (min_le_right _ _)) hC
  refine ⟨h0,h1,h2,h3,h4,by nlinarith only [hxB,hbB],h6,h7,h8,h9,?_,h11⟩
  linarith only [h10]

theorem marked_protected_inner_error_budget
    (r h:ℕ) (rho omega t epsilon etaEnd a x n ambient nW nZ:ℝ)
    (hrho:0<rho) (ho:0≤omega) (ht:0≤t) (he:0≤epsilon) (hEnd:0≤etaEnd) (ha:0≤a)
    (hx:0≤x) (hn:0≤n) (hambient:n/2≤ambient)
    (hW:omega*n/2≤nW) (hZ:omega*n/2≤nZ)
    (hExt:(1+h*(24+3*(r+5:ℝ)))*x≤epsilon*(omega/2))
    (hEndpoint:2*(1+h*(24+3*(r+5:ℝ)))*x≤etaEnd*a/2)
    (hGap:(3+2/rho+h*(24+3*(r+5:ℝ)))*x≤t*omega/16)
    (etaE errR0 errI0 errParent removedRows removedHubs exceptional:ℝ)
    (hEta:0≤etaE) (hEtaMax:etaE≤x)
    (hR:errR0≤x*n) (hI:errI0≤x*n) (hP:errParent≤x*n)
    (hRows:removedRows≤x*n) (hHubs:removedHubs≤x*n)
    (hException:exceptional≤t*omega*n/16):
    let errR:=errR0+h*(24*etaE*n+3*(r+5:ℝ)*etaE*n)
    let errI:=errI0+h*(6*etaE*n)
    let deltaParent:=errParent+removedRows+2*removedHubs/rho;
    errR≤epsilon*nW∧errI≤epsilon*nZ∧
    2*errR≤etaEnd*(a*ambient)∧2*errI≤etaEnd*(a*ambient)∧
    errR+exceptional+deltaParent≤t*omega*ambient/4∧
    errI≤t*omega*ambient/4:=by
  intro errR errI deltaParent
  let C:ℝ:=1+h*(24+3*(r+5:ℝ))
  have hhn:0≤(h:ℝ):=Nat.cast_nonneg _
  have hrn:0≤(r:ℝ):=Nat.cast_nonneg _
  have hEn:=mul_le_mul_of_nonneg_right hEtaMax hn
  have hcoef:0≤h*(24+3*(r+5:ℝ)):=by positivity
  have hmul:=mul_le_mul_of_nonneg_left hEn hcoef
  have hER:errR≤C*x*n:=by dsimp [errR,C];nlinarith only [hR,hmul]
  have h6coef:6*(h:ℝ)≤h*(24+3*(r+5:ℝ)):=by
    nlinarith only [hhn,mul_nonneg hhn hrn]
  have hmulI:=mul_le_mul_of_nonneg_left hEn (show 0≤6*(h:ℝ) by positivity)
  have hcompare:=mul_le_mul_of_nonneg_right h6coef (show 0≤x*n by positivity)
  have hEI:errI≤C*x*n:=by dsimp [errI,C];nlinarith only [hI,hmulI,hcompare]
  have hLoss:=mul_le_mul_of_nonneg_left hHubs (show 0≤2/rho by positivity)
  have hDP:deltaParent≤(2+2/rho)*x*n:=by
    calc
      deltaParent=errParent+removedRows+(2/rho)*removedHubs:=by dsimp [deltaParent];ring
      _ ≤ x*n+x*n+(2/rho)*(x*n):=add_le_add (add_le_add hP hRows) hLoss
      _ = (2+2/rho)*x*n:=by ring
  have hExtn:=mul_le_mul_of_nonneg_right hExt hn
  have hEndn:=mul_le_mul_of_nonneg_right hEndpoint hn
  have hGapn:=mul_le_mul_of_nonneg_right hGap hn
  have hW':=mul_le_mul_of_nonneg_left hW he
  have hZ':=mul_le_mul_of_nonneg_left hZ he
  have hA':=mul_le_mul_of_nonneg_left hambient (show 0≤etaEnd*a by positivity)
  have hG':=mul_le_mul_of_nonneg_left hambient (show 0≤t*omega by positivity)
  have hPos:0≤(2+2/rho)*x*n:=by positivity
  change C*x*n≤epsilon*(omega/2)*n at hExtn
  change 2*C*x*n≤(etaEnd*a/2)*n at hEndn
  have hGapn':(C+2+2/rho)*x*n≤t*omega*n/16:=by
    dsimp [C];nlinarith only [hGapn]
  refine ⟨by nlinarith only [hER,hExtn,hW'],by nlinarith only [hEI,hExtn,hZ'],
    by nlinarith only [hER,hEndn,hA'],by nlinarith only [hEI,hEndn,hA'],
    by nlinarith only [hER,hDP,hException,hGapn',hG'],?_⟩
  have htw:0≤t*omega*n:=by positivity
  nlinarith only [hEI,hGapn',hG',hPos,htw]

theorem marked_protected_inner_exception_order
    (t omega:ℝ) (ht:0<t) (ho:0<omega) (d:ℕ):
    ∃ N:ℕ,1≤N∧∀ n:ℕ,N≤n→6*(d:ℝ)+1≤t*omega*n/16:=by
  obtain ⟨N,hN⟩:=exists_nat_gt (max 1 (16*(6*(d:ℝ)+1)/(t*omega)))
  have hN1:1<(N:ℝ):=(le_max_left _ _).trans_lt hN
  refine ⟨N,by exact_mod_cast hN1.le,?_⟩
  intro n hn
  have hn':(N:ℝ)≤n:=by exact_mod_cast hn
  have hh:16*(6*(d:ℝ)+1)/(t*omega)<n:=(le_max_right _ _).trans_lt (hN.trans_le hn')
  have hh':16*(6*(d:ℝ)+1)<(n:ℝ)*(t*omega):=(div_lt_iff₀ (by positivity)).mp hh
  nlinarith only [hh']

end Oberwolfach
