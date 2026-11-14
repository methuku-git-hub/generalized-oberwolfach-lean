module

public import Oberwolfach.LongPreparationBadGraphBounds

@[expose] public section
/-! The explicit preparation hierarchy yields the maximum-degree and
edge-count bounds required by the bad-edge assignment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem long_preparation_bad_graph_margins
    (P Bad Unused Unassigned:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (hd:1≤d) (I:Finset V)
    (α θ ε lam t C₀:ℝ) (hα:0<α) (hθ:0≤θ) (hθhi:θ≤1/100)
    (he:0≤ε) (hC:1≤C₀) (hehi:ε≤α/(1000*C₀))
    (hlam:0≤lam) (hlamhi:lam≤α/128) (ht:0≤t) (htbound:t≤lam*Fintype.card V)
    (hn:(1536*(d:ℝ))/α≤Fintype.card V)
    (hI:(I.card:ℝ)≤ε*Fintype.card V)
    (hA:∀v∈I,(Unassigned.degree v:ℝ)≤2*θ*I.card+t)
    (hB:∀v∈I,(Unused.degree v:ℝ)≤lam*Fintype.card V)
    (hSub:Bad≤(spanningRestriction Unassigned I ⊔ spanningRestriction Unused I) ⊔
      longPreparationIneligibleGraph P π d):
    (∀v,(Bad.degree v:ℝ)≤(α/16)*Fintype.card V) ∧
    (Bad.edgeFinset.card:ℝ)≤(θ*ε^2+lam*ε)*(Fintype.card V:ℝ)^2+24*d*Fintype.card V:=by
  let n:ℝ:=Fintype.card V
  let a:ℝ:=2*θ*I.card+t
  let b:ℝ:=lam*n
  have hn0:0≤n:=by dsimp [n];positivity
  have hI0:(0:ℝ)≤I.card:=by positivity
  have ha:0≤a:=by dsimp [a];positivity
  have hb:0≤b:=by dsimp [b];positivity
  have hh:=long_preparation_bad_graph_bounds P Bad Unused Unassigned π d I a b ha hb hA hB hSub
  have hecoarse:ε≤α/1000:=by
    have hx:α/(1000*C₀)≤α/1000:=div_le_div_of_nonneg_left hα.le (by positivity) (by nlinarith)
    exact hehi.trans hx
  have htheta:2*θ*ε≤α/64:=by
    have hh₁:=mul_le_mul_of_nonneg_right hθhi he
    nlinarith
  have hnbound:48*(d:ℝ)≤(α/32)*n:=by
    have hh₁:1536*(d:ℝ)≤n*α:=(div_le_iff₀ hα).mp hn
    nlinarith
  have hdreal:(1:ℝ)≤d:=by exact_mod_cast hd
  have hf:(6*(d:ℝ)+2)≤48*d:=by linarith
  have hab:a+b≤(2*θ*ε+2*lam)*n:=by
    have hI':(I.card:ℝ)≤ε*n:=hI
    have hh₁:=mul_le_mul_of_nonneg_left hI' (show 0≤2*θ by positivity)
    dsimp [a,b,n] at *
    nlinarith
  constructor
  · intro v
    have hv:=hh.1 v
    have hcoeff:2*θ*ε+2*lam≤α/32:=by linarith
    have hsmall:=mul_le_mul_of_nonneg_right hcoeff hn0
    have hfd:(6*d+2:ℕ)≤48*(d:ℝ):=by push_cast;exact hf
    dsimp [n] at *
    linarith
  · have hprod:(I.card:ℝ)*(a+b)≤(ε*n)*((2*θ*ε+2*lam)*n):=by
      have hx:0≤a+b:=add_nonneg ha hb
      have hy:0≤ε*n:=mul_nonneg he hn0
      exact mul_le_mul hI hab hx hy
    have hfd:(6*d+2:ℕ)*(Fintype.card V:ℝ)≤48*(d:ℝ)*n:=by
      have h:=mul_le_mul_of_nonneg_right hf hn0
      dsimp [n] at *
      push_cast
      linarith
    have hsum:=hh.2
    dsimp [n] at *
    push_cast at hsum
    nlinarith [hprod,hfd]
end Oberwolfach
