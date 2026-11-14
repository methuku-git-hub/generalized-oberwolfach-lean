module

public import Oberwolfach.MarkedActiveReferenceBudgets

@[expose] public section

/-! A simultaneous positive choice for every global active-host tolerance.
There is no dependence on the ambient order or on the separation radius. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators
namespace Oberwolfach

private theorem finite_positive_linear_scale {I:Type} [Fintype I]
    (a b:I→ℝ) (ha:∀ i,0≤a i) (hb:∀ i,0<b i):
    ∃ k:ℝ,0<k∧∀ x:ℝ,0≤x→x≤k→∀ i,a i*x≤b i:=by
  classical
  let C:ℝ:=1+∑ i,a i/b i
  have hsum:0≤∑ i,a i/b i:=Finset.sum_nonneg (fun i _=>div_nonneg (ha i) (hb i).le)
  have hC:0<C:=by dsimp [C];linarith
  refine ⟨1/C,by positivity,?_⟩
  intro x hx hxk i
  have hi:a i/b i≤∑ j,a j/b j:=Finset.single_le_sum
    (fun j _=>div_nonneg (ha j) (hb j).le) (Finset.mem_univ i)
  have hiC:a i/b i≤C:=by dsimp [C];linarith
  have hi':a i≤C*b i:=(div_le_iff₀ (hb i)).mp hiC
  have hix:=mul_le_mul_of_nonneg_left hxk (ha i)
  apply hix.trans
  rw [mul_one_div]
  apply (div_le_iff₀ hC).mpr
  nlinarith only [hi']

theorem marked_active_reference_scale_exists
    (r h:ℕ) (omega gamma p0 beta epsA deltaSp eta0 Bbar rho deltaCut hcut:ℝ)
    (ho:0<omega) (hg:0<gamma) (hp:0<p0) (hb:0<beta) (he:0<epsA)
    (hs:0<deltaSp) (heta:0<eta0) (hB:0≤Bbar) (hrho:0<rho)
    (hdc:0<deltaCut) (hhc:0<hcut):
    ∃ kappa0:ℝ,0<kappa0∧∀ kappa:ℝ,0≤kappa→kappa≤kappa0→
    8*kappa≤epsA∧3*kappa≤gamma*p0^2∧
    8*(r+5:ℝ)*kappa≤12*beta∧(1+2*(r+5:ℝ))*kappa≤28*beta∧
    2*(2+2*(h:ℝ))*kappa≤deltaSp∧2*(2+(h:ℝ))*kappa≤deltaSp*p0^2*omega∧
    (1+2*(r+5:ℝ)^3*Bbar+66*(r+5:ℝ)^4*Bbar)*kappa≤eta0∧
    kappa≤min (gamma/128) (p0/128)∧2*kappa≤gamma*p0/8∧
    kappa≤deltaCut*omega/2∧(1+2/omega)*kappa≤14*hcut∧
    kappa≤1/4∧kappa≤gamma*rho/16∧kappa≤omega/2∧kappa≤gamma/4:=by
  let a:Fin 15→ℝ:=![8,3,8*(r+5:ℝ),1+2*(r+5:ℝ),2*(2+2*(h:ℝ)),2*(2+(h:ℝ)),
    1+2*(r+5:ℝ)^3*Bbar+66*(r+5:ℝ)^4*Bbar,1,2,1,1+2/omega,1,1,1,1]
  let b:Fin 15→ℝ:=![epsA,gamma*p0^2,12*beta,28*beta,deltaSp,deltaSp*p0^2*omega,eta0,
    min (gamma/128) (p0/128),gamma*p0/8,deltaCut*omega/2,14*hcut,1/4,gamma*rho/16,omega/2,gamma/4]
  have ha:∀ i,0≤a i:=by intro i;fin_cases i <;> dsimp [a] <;> positivity
  have hb':∀ i,0<b i:=by intro i;fin_cases i <;> dsimp [b] <;> positivity
  obtain ⟨k,hk,hall⟩:=finite_positive_linear_scale a b ha hb'
  refine ⟨k,hk,?_⟩
  intro kappa hkappa hkk
  have hall':=hall kappa hkappa hkk
  have h0:=hall' 0;have h1:=hall' 1;have h2:=hall' 2;have h3:=hall' 3
  have h4:=hall' 4;have h5:=hall' 5;have h6:=hall' 6;have h7:=hall' 7
  have h8:=hall' 8;have h9:=hall' 9;have h10:=hall' 10;have h11:=hall' 11
  have h12:=hall' 12;have h13:=hall' 13;have h14:=hall' 14
  simpa [a,b] using
    And.intro h0 (And.intro h1 (And.intro h2 (And.intro h3 (And.intro h4 (And.intro h5
      (And.intro h6 (And.intro h7 (And.intro h8 (And.intro h9 (And.intro h10
        (And.intro h11 (And.intro h12 (And.intro h13 h14)))))))))))))

end Oberwolfach
