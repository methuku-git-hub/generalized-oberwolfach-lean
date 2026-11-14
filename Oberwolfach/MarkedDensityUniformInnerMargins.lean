module

public import Oberwolfach.MarkedInnerFactorDeletionTolerance
public import Oberwolfach.MarkedProtectedInnerBudgets

@[expose] public section
/-! Two cover-down choices made from fixed lower density bounds. Neither
choice changes a sampled profile or an actual degree target. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_inner_factor_deletion_tolerance_uniform
    (r h:ℕ) (tstar beta eta C:ℝ) (ht:0<tstar) (hb:0<beta) (he:0<eta) (hC:0≤C):
    ∃ zeta:ℝ,0<zeta ∧ ∀ t:ℝ,tstar≤t→∀ zR zS:ℝ,0≤zR→0≤zS→zR≤zeta→zS≤zeta→
    h*(zR+zS)≤t/4∧(r+5:ℝ)*(zR+zS)≤beta∧
    (r+7:ℝ)*zR+(r+4:ℝ)*zS≤beta∧
    5*(r+5:ℝ)^4*C*(2*zR+zS)≤eta/2:=by
  obtain ⟨zeta,hz,hbudget⟩:=marked_inner_factor_deletion_tolerance r h tstar beta eta C ht hb he hC
  refine ⟨zeta,hz,?_⟩
  intro t hts zR zS hzR hzS hR hS
  obtain ⟨h1,h2,h3,h4⟩:=hbudget zR zS hzR hzS hR hS
  exact ⟨h1.trans (by linarith),h2,h3,h4⟩

theorem marked_protected_inner_exception_order_uniform
    (tstar omegastar:ℝ) (ht:0<tstar) (ho:0<omegastar) (d:ℕ):
    ∃ N:ℕ,1≤N ∧ ∀ t omega:ℝ,tstar ≤ t → omegastar ≤ omega →
      ∀ n:ℕ,N≤n→6*(d:ℝ)+1≤t*omega*n/16:=by
  obtain ⟨N,hN,hbound⟩:=marked_protected_inner_exception_order tstar omegastar ht ho d
  refine ⟨N,hN,?_⟩
  intro t omega hts hos n hn
  have ht0:0≤t:=ht.le.trans hts
  have ho0:0≤omegastar:=ho.le
  have hprod:tstar*omegastar≤t*omega:=mul_le_mul hts hos ho0 ht0
  have hh:=mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg n)
  exact (hbound n hn).trans (by linarith)
theorem marked_protected_inner_budget_scale_uniform
    (r K h:ℕ) (omegastar kappa rhostar tstar zeta epsilon etaEnd astar theta etaEmax:ℝ)
    (ho:0<omegastar) (hk:0<kappa) (hrho:0<rhostar) (ht:0<tstar) (hz:0<zeta)
    (he:0<epsilon) (hEnd:0<etaEnd) (ha:0<astar) (hth:0<theta) (hmax:0<etaEmax):
    ∃ delta:ℝ,0<delta ∧ ∀ omega rho t a:ℝ,omegastar≤omega → rhostar≤rho → tstar≤t → astar≤a →
      ∀ x:ℝ,0≤x→x≤delta→
    (4*K+3*r+50:ℝ)*x≤kappa/2∧24*x≤zeta*(omega/2)∧3*(r+5:ℝ)*x≤zeta*(omega/2)∧
    (1+h*(24+3*(r+5:ℝ)))*x≤epsilon*(omega/2)∧
    2*(1+h*(24+3*(r+5:ℝ)))*x≤etaEnd*a/2∧
    (3+2/rho+h*(24+3*(r+5:ℝ)))*x≤t*omega/16∧
    8*x≤theta∧(r+6:ℝ)*x≤theta/8∧(r+6:ℝ)*(96+3*(r+5:ℝ))*x≤theta/4∧
    x≤etaEmax∧x≤omega/4∧x≤kappa:=by
  obtain ⟨δ,hδ,hbound⟩:=marked_protected_inner_budget_scale r K h omegastar kappa rhostar tstar zeta epsilon etaEnd astar theta etaEmax
    ho hk hrho ht hz he hEnd ha hth hmax
  refine ⟨δ,hδ,?_⟩
  intro omega rho t a hω hρ ht' ha' x hx hxd
  obtain ⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11⟩:=hbound x hx hxd
  have hω0:0≤omega:=ho.le.trans hω
  have ht0:0≤t:=ht.le.trans ht'
  have htω:tstar*omegastar≤t*omega:=mul_le_mul ht' hω ho.le ht0
  have hρpos:0<rho:=hrho.trans_le hρ
  have hi:1/rho≤1/rhostar:=one_div_le_one_div_of_le hrho hρ
  have hi2:2/rho≤2/rhostar:=by
    have hh:=mul_le_mul_of_nonneg_left hi (show (0:ℝ)≤2 by norm_num)
    simpa only [mul_one_div] using hh
  have hc:(3+2/rho+h*(24+3*(r+5:ℝ)))≤(3+2/rhostar+h*(24+3*(r+5:ℝ))):=by linarith only [hi2]
  have hxC:=mul_le_mul_of_nonneg_right hc hx
  have hζω:=mul_le_mul_of_nonneg_left hω hz.le
  have heω:=mul_le_mul_of_nonneg_left hω he.le
  have hEa:=mul_le_mul_of_nonneg_left ha' hEnd.le
  refine ⟨b0,by nlinarith only [b1,hζω],by nlinarith only [b2,hζω],by nlinarith only [b3,heω],
    by nlinarith only [b4,hEa],by nlinarith only [b5,hxC,htω],b6,b7,b8,b9,by linarith,b11⟩

end Oberwolfach
