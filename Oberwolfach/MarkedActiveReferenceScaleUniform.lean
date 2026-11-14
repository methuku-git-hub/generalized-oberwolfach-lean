module

public import Oberwolfach.MarkedActiveReferenceScale

@[expose] public section
/-! A single accuracy works for all later actual density parameters above
fixed positive lower bounds. The actual parameters remain in every bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_active_reference_scale_uniform
    (r h:ℕ) (omega₀ gamma p0 beta epsA deltaSp eta0 Bbar rho₀ deltaCut₀ hcut₀:ℝ)
    (ho:0<omega₀) (hg:0<gamma) (hp:0<p0) (hb:0<beta) (he:0<epsA)
    (hs:0<deltaSp) (heta:0<eta0) (hB:0≤Bbar) (hrho:0<rho₀)
    (hdc:0<deltaCut₀) (hhc:0<hcut₀):
    ∃ kappa0:ℝ,0<kappa0 ∧ ∀ omega rho deltaCut hcut:ℝ,
    omega₀≤omega → rho₀≤rho → deltaCut₀≤deltaCut → hcut₀≤hcut →
    ∀ kappa:ℝ,0≤kappa→kappa≤kappa0→
    8*kappa≤epsA∧3*kappa≤gamma*p0^2∧
    8*(r+5:ℝ)*kappa≤12*beta∧(1+2*(r+5:ℝ))*kappa≤28*beta∧
    2*(2+2*(h:ℝ))*kappa≤deltaSp∧2*(2+(h:ℝ))*kappa≤deltaSp*p0^2*omega∧
    (1+2*(r+5:ℝ)^3*Bbar+66*(r+5:ℝ)^4*Bbar)*kappa≤eta0∧
    kappa≤min (gamma/128) (p0/128)∧2*kappa≤gamma*p0/8∧
    kappa≤deltaCut*omega/2∧(1+2/omega)*kappa≤14*hcut∧
    kappa≤1/4∧kappa≤gamma*rho/16∧kappa≤omega/2∧kappa≤gamma/4:=by
  obtain ⟨κ,hκ,hscale⟩:=marked_active_reference_scale_exists r h omega₀ gamma p0 beta epsA deltaSp eta0 Bbar rho₀ deltaCut₀ hcut₀
    ho hg hp hb he hs heta hB hrho hdc hhc
  refine ⟨κ,hκ,?_⟩
  intro omega rho deltaCut hcut hω hρ hδ hh kappa hk hkk
  obtain ⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14⟩:=hscale kappa hk hkk
  have homega:0<omega:=ho.trans_le hω
  have hδprod:deltaCut₀*omega₀≤deltaCut*omega:=mul_le_mul hδ hω ho.le (hdc.le.trans hδ)
  have hi:1/omega≤1/omega₀:=one_div_le_one_div_of_le ho hω
  have hi2:2/omega≤2/omega₀:=by
    have hh:=mul_le_mul_of_nonneg_left hi (show (0:ℝ)≤2 by norm_num)
    simpa only [mul_one_div] using hh
  have hbcoef:1+2/omega≤1+2/omega₀:=by linarith only [hi2]
  have hcoef:=mul_le_mul_of_nonneg_right hbcoef hk
  have hpω:=mul_le_mul_of_nonneg_left hω (show 0≤deltaSp*p0^2 by positivity)
  have hgρ:=mul_le_mul_of_nonneg_left hρ hg.le
  refine ⟨b0,b1,b2,b3,b4,by nlinarith only [b5,hpω],b6,b7,b8,
    by nlinarith only [b9,hδprod],by nlinarith only [b10,hcoef,hh],b11,
    by nlinarith only [b12,hgρ],by linarith,b14⟩
end Oberwolfach
