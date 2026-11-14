module

public import Oberwolfach.MarkedInnerFactorDeletionTolerance
public import Oberwolfach.MarkedProtectedActiveBalanceInputs

@[expose] public section

/-! The local error and packing allowances are chosen after the actual
active-factor and boundary tolerances. One positive scale satisfies every
listed inequality before any graph order or sample is chosen. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped BigOperators
namespace Oberwolfach

private theorem protected_local_positive_linear_scale {I:Type} [Fintype I]
    (a b:I→ ℝ) (ha:∀ i,0≤a i) (hb:∀ i,0<b i):
    ∃ k:ℝ,0<k∧∀ x:ℝ,0≤x→ x≤k→ ∀ i,a i*x≤b i:=by
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

theorem marked_protected_local_scale_exists
    (r K h:ℕ) (iota kappa t zeta epsilon etaEnd a theta etaEmax:ℝ)
    (hi:0< iota) (hk:0<kappa) (ht:0<t) (hz:0<zeta) (he:0<epsilon)
    (hEnd:0<etaEnd) (ha:0<a) (hth:0<theta) (hmax:0<etaEmax):
    ∃ delta:ℝ,0<delta∧∀ x:ℝ,0≤x→ x≤delta→ 
    (4*K+3*r+50:ℝ)*x≤kappa/2∧24*x≤zeta*iota∧3*(r+5:ℝ)*x≤zeta*iota∧
    (1+h*(24+3*(r+5:ℝ)))*x≤epsilon*iota∧
    2*(1+h*(24+3*(r+5:ℝ)))*x≤etaEnd*a/2∧
    (3+h*(24+3*(r+5:ℝ)))*x≤t*iota/4∧8*x≤theta∧
    (r+6:ℝ)*x≤theta/8∧(r+6:ℝ)*(96+3*(r+5:ℝ))*x≤theta/4∧
    x≤etaEmax∧x≤ iota/2∧x≤kappa:=by
  let A:Fin 12→ ℝ:=![4*K+3*r+50,24,3*(r+5:ℝ),1+h*(24+3*(r+5:ℝ)),
    2*(1+h*(24+3*(r+5:ℝ))),3+h*(24+3*(r+5:ℝ)),8,r+6,
    (r+6:ℝ)*(96+3*(r+5:ℝ)),1,1,1]
  let B:Fin 12→ ℝ:=![kappa/2,zeta*iota,zeta*iota,epsilon*iota,etaEnd*a/2,
    t*iota/4,theta,theta/8,theta/4,etaEmax,iota/2,kappa]
  have hA:∀ i,0≤A i:=by intro i;fin_cases i <;> dsimp [A] <;> positivity
  have hB:∀ i,0<B i:=by intro i;fin_cases i <;> dsimp [B] <;> positivity
  obtain ⟨delta,hd,hall⟩:=protected_local_positive_linear_scale A B hA hB
  refine ⟨delta,hd,?_⟩
  intro x hx hxd
  have hall':=hall x hx hxd
  have h0:=hall' 0;have h1:=hall' 1;have h2:=hall' 2;have h3:=hall' 3
  have h4:=hall' 4;have h5:=hall' 5;have h6:=hall' 6;have h7:=hall' 7
  have h8:=hall' 8;have h9:=hall' 9;have h10:=hall' 10;have h11:=hall' 11
  simpa [A,B] using
    And.intro h0 (And.intro h1 (And.intro h2 (And.intro h3 (And.intro h4 (And.intro h5
      (And.intro h6 (And.intro h7 (And.intro h8 (And.intro h9 (And.intro h10 h11))))))))))

end Oberwolfach
