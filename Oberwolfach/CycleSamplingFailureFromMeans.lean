module

public import Oberwolfach.CycleSamplingFiniteUnionMargin
public import Oberwolfach.CycleSamplingPointwiseTails

@[expose] public section
/-! The concrete fixed-test failure sum is small under the displayed
quadratic vertex-mean and linear pair-mean bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cycle_sampling_failure_from_means
    (θ a q d:ℝ) (hθ:0<θ) (ha:0<a) (hq:0≤q) (hd:0<d)
    (hscale:2*Real.exp 1*q≤d):
    ∃ N:ℕ,∀ (V:Type) [Fintype V],N≤Fintype.card V→
    ∀ (S:Finset (V×V)) (mV:V→ℝ) (mP:V×V→ℝ),
    (∀ v,a*(Fintype.card V:ℝ)^2≤mV v)→
    (∀ z∈S,0<mP z ∧ mP z≤q*Fintype.card V)→
    (∑ v,2*Real.exp (-θ^2*mV v/3))+
      (∑ z∈S,(Real.exp 1*mP z/(d*Fintype.card V))^(d*Fintype.card V))<1:=by
  let c:=θ^2*a/3
  let b:=Real.log 2*d
  have hc:0<c:=by dsimp [c];positivity
  have hb:0<b:=by dsimp [b];positivity
  obtain ⟨N,hN⟩:=cycle_sampling_finite_union_margin c b hc hb
  refine ⟨max N 1,?_⟩
  intro V _ hn S mV mP hV hP
  have hnpos:0<(Fintype.card V:ℝ):=by
    exact_mod_cast (show 0<Fintype.card V by omega)
  let errV:=fun v=>2*Real.exp (-θ^2*mV v/3)
  let errP:=fun z=>(Real.exp 1*mP z/(d*Fintype.card V))^(d*Fintype.card V)
  apply hN V ((le_max_left N 1).trans hn) S errV errP
  · intro v
    apply cycle_sampling_relative_tail_bound θ (mV v) c (Fintype.card V)
    have hh:=mul_le_mul_of_nonneg_left (hV v) (sq_nonneg θ)
    dsimp [c];nlinarith only [hh]
  · intro z hz
    have hm:0<mP z:=(hP z hz).1
    have ht:0<d*(Fintype.card V:ℝ):=mul_pos hd hnpos
    have hhalf:Real.exp 1*mP z/(d*Fintype.card V)≤1/2:=by
      apply (div_le_iff₀ ht).2
      have h1:=mul_le_mul_of_nonneg_left (hP z hz).2 (Real.exp_pos 1).le
      have h2:=mul_le_mul_of_nonneg_right hscale hnpos.le
      nlinarith only [h1,h2]
    have hh:=cycle_sampling_large_tail_half (mP z) (d*Fintype.card V) hm ht hhalf
    dsimp [errP,b] at *
    convert hh using 1 <;> ring_nf
end Oberwolfach
