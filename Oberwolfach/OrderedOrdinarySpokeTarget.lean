module

public import Oberwolfach.OrderedOrdinarySeedExpectations
public import Oberwolfach.OrderedOrdinaryWeightedSums

@[expose] public section
/-! The target for one length is its supplied hub coefficient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem orderedOrdinary_seed_spoke_target
    (P:SimpleGraph V) (π:Equiv.Perm V) (p k:ℝ) (hp:0<p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (r:ℕ) (hr:3≤r) (g:Γ) (j:Color) (D τ:ℝ) (hD:0<D) (hspos:∀ u,0<s u j)
    (η:U→ℝ) (hη:∀ u,0≤η u) (weight:(Fin r→V)→ℝ)
    (hsupport:∀ W:OrderedOrdinaryWheel (U:=U) π (3*d) r,weight W.1.val≠0→
      ∀ i:Fin r,P.Adj (W.1.val i) (W.1.val (cycleNext i)))
    (v:V) (u:U)
    (hpos:∀ i:Fin r,(1-τ)*D≤(∑ C:{C:Fin r→V // PermutationSeparated π (3*d) C},if C.val i=v then weight C.val else 0) ∧
      (∑ C:{C:Fin r→V // PermutationSeparated π (3*d) C},if C.val i=v then weight C.val else 0)≤(1+τ)*D):
    let seed:=fun W:OrderedOrdinaryWheel (U:=U) π (3*d) r=>η W.2*weight W.1.val/((r:ℝ)*D*p^r*(s W.2 j)^(r-1))
    let mean:=(FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk hsum d hd q hq hQ s hs hS)).expectation
      (fun σ=>resourcePatternLoad orderedOrdinaryResources seed (fun _ _=>true) (Sum.inr (v,u)) (orderedOrdinaryResourceState P π d g j σ));
    (1-τ)*η u≤mean ∧ mean≤(1+τ)*η u:=by
  intro seed mean
  let S:ℝ:=∑ i:Fin r,∑ C:{C:Fin r→V // PermutationSeparated π (3*d) C},if C.val i=v then weight C.val else 0
  have hrR:(0:ℝ)<r:=by exact_mod_cast (show 0<r by omega)
  have hsumlo:(r:ℝ)*((1-τ)*D)≤S:=by
    have hh:∑ _i:Fin r,(1-τ)*D≤S:=by
      apply Finset.sum_le_sum
      intro i _
      exact (hpos i).1
    simpa [S] using hh
  have hsumhi:S≤(r:ℝ)*((1+τ)*D):=by
    have hh:S≤∑ _i:Fin r,(1+τ)*D:=by
      apply Finset.sum_le_sum
      intro i _
      exact (hpos i).2
    simpa [S] using hh
  have hmean:=orderedOrdinary_seed_spoke_expectation P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort r hr g j D hD hspos η weight hsupport v u
  change mean = _ at hmean
  have heq:mean=S*(η u/((r:ℝ)*D)):=by
    rw [hmean]
    have hsum:=orderedOrdinary_spoke_weighted_sum (π:=π) (b:=3*d) weight v u
    calc
      _ = (∑ W:OrderedOrdinaryWheel (U:=U) π (3*d) r,if Sum.inr (v,u)∈orderedOrdinaryResources W then weight W.1.val else 0)*(η u/((r:ℝ)*D)):=by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro W _
        split_ifs <;> simp only [mul_div_assoc,zero_mul] <;> ring
      _ = _ := by
        have hh:(∑ W:OrderedOrdinaryWheel (U:=U) π (3*d) r,if Sum.inr (v,u)∈orderedOrdinaryResources W then weight W.1.val else 0)=S:=by
          dsimp [S]
          convert hsum using 1
        rw [hh]
  have hfac:0≤η u/((r:ℝ)*D):=div_nonneg (hη u) (mul_nonneg hrR.le hD.le)
  have hlo:=mul_le_mul_of_nonneg_right hsumlo hfac
  have hhi:=mul_le_mul_of_nonneg_right hsumhi hfac
  have hlo':((r:ℝ)*((1-τ)*D))*(η u/((r:ℝ)*D))=(1-τ)*η u:=by
    field_simp
    <;> ring
  have hhi':((r:ℝ)*((1+τ)*D))*(η u/((r:ℝ)*D))=(1+τ)*η u:=by
    field_simp
    <;> ring
  rw [←heq,hlo'] at hlo
  rw [←heq,hhi'] at hhi
  exact ⟨hlo,hhi⟩
end Oberwolfach
