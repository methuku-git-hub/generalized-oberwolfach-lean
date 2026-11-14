module

public import Oberwolfach.OrderedOrdinaryWheelMarginal

@[expose] public section
/-! Root-omitted seed means with the original fixed hub coefficients. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

section
variable (P:SimpleGraph V) (π:Equiv.Perm V) (p k:ℝ) (hp:0<p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (r:ℕ) (hr:3≤r) (g:Γ) (j:Color) (D:ℝ) (hD:0<D) (hspos:∀ u,0<s u j)
    (η:U→ℝ) (weight:(Fin r→V)→ℝ)
    (hsupport:∀ W:OrderedOrdinaryWheel (U:=U) π (3*d) r,weight W.1.val≠0→
      ∀ i:Fin r,P.Adj (W.1.val i) (W.1.val (cycleNext i)))

local notation "μ" => FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk hsum d hd q hq hQ s hs hS)
local notation "seed" => (fun W:OrderedOrdinaryWheel (U:=U) π (3*d) r => η W.2*weight W.1.val/((r:ℝ)*D*p^r*(s W.2 j)^(r-1)))
local notation "L" => (fun root σ => resourcePatternLoad orderedOrdinaryResources seed (fun _ _=>true) root (orderedOrdinaryResourceState P π d g j σ))

include hr hnoshort hD hspos hsupport

theorem orderedOrdinary_seed_spoke_expectation (v:V) (u:U):
    (μ).expectation (L (Sum.inr (v,u))) =
      ∑ W:OrderedOrdinaryWheel (U:=U) π (3*d) r,if Sum.inr (v,u)∈orderedOrdinaryResources W then η u*weight W.1.val/((r:ℝ)*D) else 0 :=by
  rw [orderedOrdinary_potential_expectation P π p k hp.le hk hsum d hd q hq hQ s hs hS hnoshort r hr seed g j]
  apply Finset.sum_congr rfl
  intro W _
  by_cases hroot:Sum.inr (v,u)∈orderedOrdinaryResources W
  · have hu:W.2=u:=by
      obtain ⟨i,hi⟩:=(orderedOrdinaryResources_spoke W (v,u)).mp hroot
      exact congrArg Prod.snd hi
    simp only [hroot,ite_true]
    by_cases hw:weight W.1.val=0
    · simp [hw]
    · have hprod:=Finset.prod_congr rfl (fun a (ha:a∈orderedOrdinaryResources W\{Sum.inr (v,u)})=>
        orderedOrdinary_marginal_on_candidate P d hr W (hsupport W hw) p k q s g j a (Finset.mem_sdiff.mp ha).1)
      rw [hprod,orderedOrdinary_spoke_omitted_product W hr p (s W.2 j) (ne_of_gt (hspos W.2)) (v,u) hroot,hu]
      have hr0:(r:ℝ)≠0:=by exact_mod_cast (show r≠0 by omega)
      field_simp [hr0,hD.ne',hp.ne',ne_of_gt (hspos u)]
  · simp [hroot]

theorem orderedOrdinary_seed_rim_expectation (x y:V):
    (μ).expectation (L (Sum.inl (x,y))) =
      ∑ W:OrderedOrdinaryWheel (U:=U) π (3*d) r,if Sum.inl (x,y)∈orderedOrdinaryResources W then η W.2*weight W.1.val*s W.2 j/((r:ℝ)*D*p) else 0 :=by
  rw [orderedOrdinary_potential_expectation P π p k hp.le hk hsum d hd q hq hQ s hs hS hnoshort r hr seed g j]
  apply Finset.sum_congr rfl
  intro W _
  by_cases hroot:Sum.inl (x,y)∈orderedOrdinaryResources W
  · simp only [hroot,ite_true]
    by_cases hw:weight W.1.val=0
    · simp [hw]
    · have hprod:=Finset.prod_congr rfl (fun a (ha:a∈orderedOrdinaryResources W\{Sum.inl (x,y)})=>
        orderedOrdinary_marginal_on_candidate P d hr W (hsupport W hw) p k q s g j a (Finset.mem_sdiff.mp ha).1)
      rw [hprod,orderedOrdinary_rim_omitted_product W hr p (s W.2 j) hp.ne' (x,y) hroot]
      have hr0:(r:ℝ)≠0:=by exact_mod_cast (show r≠0 by omega)
      have hrpow:r-1+1=r:=Nat.sub_add_cancel (by omega)
      have hpPow:p^r=p*p^(r-1):=by rw [←pow_succ',hrpow]
      have hsPow:(s W.2 j)^r=s W.2 j*(s W.2 j)^(r-1):=by rw [←pow_succ',hrpow]
      rw [hpPow,hsPow]
      field_simp [hr0,hD.ne',hp.ne',ne_of_gt (hspos W.2)]
      <;> ring
  · simp [hroot]
end
end Oberwolfach
