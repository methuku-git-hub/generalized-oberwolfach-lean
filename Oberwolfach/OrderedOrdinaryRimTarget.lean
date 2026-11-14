module

public import Oberwolfach.OrderedOrdinarySeedExpectations
public import Oberwolfach.OrderedOrdinaryWeightedSums

@[expose] public section
/-! The directed-rim target for one length uses the original sum of hub
coefficients times their spoke probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem orderedOrdinary_seed_rim_target
    (P:SimpleGraph V) (π:Equiv.Perm V) (p k:ℝ) (hp:0<p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (r:ℕ) (hr:3≤r) (g:Γ) (j:Color) (D τ:ℝ) (hD:0<D) (hspos:∀ u,0<s u j)
    (η:U→ℝ) (hη:∀ u,0≤η u) (weight:(Fin r→V)→ℝ)
    (hsupport:∀ W:OrderedOrdinaryWheel (U:=U) π (3*d) r,weight W.1.val≠0→
      ∀ i:Fin r,P.Adj (W.1.val i) (W.1.val (cycleNext i)))
    (x y:V)
    (hpos:∀ i:Fin r,1-τ≤(∑ C:{C:Fin r→V // PermutationSeparated π (3*d) C},if C.val i=x ∧ C.val (cycleNext i)=y then weight C.val else 0) ∧
      (∑ C:{C:Fin r→V // PermutationSeparated π (3*d) C},if C.val i=x ∧ C.val (cycleNext i)=y then weight C.val else 0)≤1+τ):
    let seed:=fun W:OrderedOrdinaryWheel (U:=U) π (3*d) r=>η W.2*weight W.1.val/((r:ℝ)*D*p^r*(s W.2 j)^(r-1))
    let mean:=(FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk hsum d hd q hq hQ s hs hS)).expectation
      (fun σ=>resourcePatternLoad orderedOrdinaryResources seed (fun _ _=>true) (Sum.inl (x,y)) (orderedOrdinaryResourceState P π d g j σ));
    (1-τ)*(∑ u,η u*s u j)/(D*p)≤mean ∧ mean≤(1+τ)*(∑ u,η u*s u j)/(D*p):=by
  intro seed mean
  let S:ℝ:=∑ i:Fin r,∑ C:{C:Fin r→V // PermutationSeparated π (3*d) C},if C.val i=x ∧ C.val (cycleNext i)=y then weight C.val else 0
  let Q:ℝ:=∑ u,η u*s u j
  have hQ0:0≤Q:=Finset.sum_nonneg (fun u _=>mul_nonneg (hη u) (hs u j))
  have hrR:(0:ℝ)<r:=by exact_mod_cast (show 0<r by omega)
  have hsumlo:(r:ℝ)*(1-τ)≤S:=by
    have hh:∑ _i:Fin r,(1-τ)≤S:=by
      apply Finset.sum_le_sum
      intro i _
      exact (hpos i).1
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    exact hh
  have hsumhi:S≤(r:ℝ)*(1+τ):=by
    have hh:S≤∑ _i:Fin r,(1+τ):=by
      apply Finset.sum_le_sum
      intro i _
      exact (hpos i).2
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    exact hh
  have hmean:=orderedOrdinary_seed_rim_expectation P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort r hr g j D hD hspos η weight hsupport x y
  change mean = _ at hmean
  have heq:mean=S*(Q/((r:ℝ)*D*p)):=by
    rw [hmean]
    have hsum:=orderedOrdinary_rim_weighted_sum (π:=π) (b:=3*d) weight (fun u=>η u*s u j) hr x y
    calc
      _ = (∑ W:OrderedOrdinaryWheel (U:=U) π (3*d) r,if Sum.inl (x,y)∈orderedOrdinaryResources W then weight W.1.val*(η W.2*s W.2 j) else 0)/((r:ℝ)*D*p):=by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro W _
        split_ifs
        · apply congrArg (fun z:ℝ=>z/((r:ℝ)*D*p))
          ring
        · simp
      _ = _ :=by
        rw [hsum]
        dsimp [S,Q]
        ring
  have hfac:0≤Q/((r:ℝ)*D*p):=div_nonneg hQ0 (by positivity)
  have hlo:=mul_le_mul_of_nonneg_right hsumlo hfac
  have hhi:=mul_le_mul_of_nonneg_right hsumhi hfac
  have hlo':((r:ℝ)*(1-τ))*(Q/((r:ℝ)*D*p))=(1-τ)*Q/(D*p):=by
    field_simp
    <;> ring
  have hhi':((r:ℝ)*(1+τ))*(Q/((r:ℝ)*D*p))=(1+τ)*Q/(D*p):=by
    field_simp
    <;> ring
  rw [←heq,hlo'] at hlo
  rw [←heq,hhi'] at hhi
  exact ⟨hlo,hhi⟩
end Oberwolfach
