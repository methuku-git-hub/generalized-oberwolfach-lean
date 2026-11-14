module

public import Oberwolfach.LongPreparationCoefficientBalance

@[expose] public section
/-! The long preparation's density and coefficient inputs follow from its
prescribed component fractions and the displayed lower bounds on marginals. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_preparation_concrete_marginals {U I:Type} [Fintype U] [Fintype I]
    (D ρ c m θ pstar:ℝ) (hD:0<D) (hρ:0<ρ) (hc:0<c) (hm:0≤m) (hθ:θ≤1)
    (hpstar:0<pstar) (hpstarb:pstar≤1/4) (hpstarp:pstar≤ρ/8) (hpstark:pstar≤ρ/(6*c))
    (a b:U→ℝ) (f:I→U→ℝ)
    (ha:∀ u,1/(3*c)≤a u) (hb:∀ u,1/4≤b u ∧ b u≤1) (hf:∀ i u,0≤f i u)
    (hsize:ρ*D/2≤(Fintype.card U:ℝ))
    (hdef:∀ u,b u=m*a u+(1-θ)*∑ i,f i u):
    let η:=fun i u=>(1-θ)*f i u/b u
    let p:=(∑ u,b u)/D
    let k:=(∑ u,a u)/D;
    pstar≤p ∧ pstar≤k ∧ (∀ u,pstar≤b u) ∧
    (∀ i u,0≤η i u ∧ η i u≤1/b u) ∧
    (∀ u,m*a u+(∑ i,η i u)*b u=b u) ∧
    (∑ u,a u)=D*k ∧ (∑ u,b u)=D*p:=by
  intro η p k
  have ha0:∀ u,0≤a u:=by
    intro u
    have h:=ha u
    have hc0:0≤1/(3*c):=by positivity
    linarith
  have hb0:∀ u,0<b u ∧ b u≤1:=by
    intro u
    constructor
    · have h:=(hb u).1
      linarith
    · exact (hb u).2
  have hdensity:=long_preparation_density_bounds D ρ c hD hρ hc a b ha (fun u=>(hb u).1) hsize
  have hcoeff:=long_preparation_coefficient_balance D m θ hD hm hθ a b f ha0 hb0 hf hdef
  dsimp only at hcoeff
  refine ⟨hpstarp.trans hdensity.1,hpstark.trans hdensity.2,?_,hcoeff.1,hcoeff.2.1,hcoeff.2.2.1,hcoeff.2.2.2⟩
  intro u
  exact hpstarb.trans (hb u).1
end Oberwolfach
