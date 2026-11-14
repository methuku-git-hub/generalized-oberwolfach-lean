module

public import Oberwolfach.MarkedProtectedInnerBudgets

@[expose] public section

/-! The deeper-set sizes have a separate geometric allowance. They do
not have to fit the much smaller correction and weighted-profile error. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Oberwolfach

theorem marked_protected_inner_error_budget_separate_geometry
    (r h:ℕ) (rho omega t epsilon etaEnd a x n ambient nW nZ:ℝ)
    (hrho:0<rho) (ho:0≤ omega) (ht:0≤ t) (he:0≤ epsilon) (hEnd:0≤ etaEnd) (ha:0≤ a)
    (hx:0≤ x) (hn:0≤ n) (hambient:n/2≤ ambient)
    (hW:omega*n/2≤ nW) (hZ:omega*n/2≤ nZ)
    (hExt:(1+h*(24+3*(r+5:ℝ)))*x≤ epsilon*(omega/2))
    (hEndpoint:2*(1+h*(24+3*(r+5:ℝ)))*x≤ etaEnd*a/2)
    (hGap:(3+2/rho+h*(24+3*(r+5:ℝ)))*x≤ t*omega/16)
    (xiDeep:ℝ) (hDeepGap:(1+2/rho)*xiDeep≤ t*omega/32)
    (etaE errR0 errI0 errParent removedRows removedHubs exceptional:ℝ)
    (hEta:0≤ etaE) (hEtaMax:etaE≤ x)
    (hR:errR0≤ x*n) (hI:errI0≤ x*n) (hP:errParent≤ x*n)
    (hRows:removedRows≤ xiDeep*n) (hHubs:removedHubs≤ xiDeep*n)
    (hException:exceptional≤ t*omega*n/32):
    let errR:=errR0+h*(24*etaE*n+3*(r+5:ℝ)*etaE*n)
    let errI:=errI0+h*(6*etaE*n)
    let deltaParent:=errParent+removedRows+2*removedHubs/rho;
    errR≤ epsilon*nW∧ errI≤ epsilon*nZ∧ 
    2*errR≤ etaEnd*(a*ambient)∧ 2*errI≤ etaEnd*(a*ambient)∧ 
    errR+exceptional+deltaParent≤ t*omega*ambient/4∧ 
    errI≤ t*omega*ambient/4:=by
  intro errR errI deltaParent
  let C:ℝ:=1+h*(24+3*(r+5:ℝ))
  have hhn:0≤ (h:ℝ):=Nat.cast_nonneg _
  have hrn:0≤ (r:ℝ):=Nat.cast_nonneg _
  have hEn:=mul_le_mul_of_nonneg_right hEtaMax hn
  have hcoef:0≤ h*(24+3*(r+5:ℝ)):=by positivity
  have hmul:=mul_le_mul_of_nonneg_left hEn hcoef
  have hER:errR≤ C*x*n:=by dsimp [errR,C];nlinarith only [hR,hmul]
  have h6coef:6*(h:ℝ)≤ h*(24+3*(r+5:ℝ)):=by
    nlinarith only [hhn,mul_nonneg hhn hrn]
  have hmulI:=mul_le_mul_of_nonneg_left hEn (show 0≤ 6*(h:ℝ) by positivity)
  have hcompare:=mul_le_mul_of_nonneg_right h6coef (show 0≤ x*n by positivity)
  have hEI:errI≤ C*x*n:=by dsimp [errI,C];nlinarith only [hI,hmulI,hcompare]
  have hLoss:=mul_le_mul_of_nonneg_left hHubs (show 0≤ 2/rho by positivity)
  have hDP:deltaParent≤ x*n+(1+2/rho)*xiDeep*n:=by
    calc
      deltaParent=errParent+removedRows+(2/rho)*removedHubs:=by dsimp [deltaParent];ring
      _ ≤  x*n+xiDeep*n+(2/rho)*(xiDeep*n):=add_le_add (add_le_add hP hRows) hLoss
      _ = x*n+(1+2/rho)*xiDeep*n:=by ring
  have hExtn:=mul_le_mul_of_nonneg_right hExt hn
  have hEndn:=mul_le_mul_of_nonneg_right hEndpoint hn
  have hDeepGapn:=mul_le_mul_of_nonneg_right hDeepGap hn
  have hGapn:=mul_le_mul_of_nonneg_right hGap hn
  have hW':=mul_le_mul_of_nonneg_left hW he
  have hZ':=mul_le_mul_of_nonneg_left hZ he
  have hA':=mul_le_mul_of_nonneg_left hambient (show 0≤ etaEnd*a by positivity)
  have hG':=mul_le_mul_of_nonneg_left hambient (show 0≤ t*omega by positivity)
  have hPos:0≤ (1+2/rho)*x*n:=by positivity
  change C*x*n≤ epsilon*(omega/2)*n at hExtn
  change 2*C*x*n≤ (etaEnd*a/2)*n at hEndn
  have hGapn':(C+2+2/rho)*x*n≤ t*omega*n/16:=by
    dsimp [C];nlinarith only [hGapn]
  refine ⟨by nlinarith only [hER,hExtn,hW'],by nlinarith only [hEI,hExtn,hZ'],
    by nlinarith only [hER,hEndn,hA'],by nlinarith only [hEI,hEndn,hA'],
    by nlinarith only [hER,hDP,hException,hGapn',hG',hDeepGapn,hPos],?_⟩
  have htw:0≤ t*omega*n:=by positivity
  have hxn:0≤ x*n:=mul_nonneg hx hn
  nlinarith only [hEI,hGapn',hG',hPos,hxn,htw]


end Oberwolfach
