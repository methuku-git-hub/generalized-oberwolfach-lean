module

public import Oberwolfach.OrderedOrdinarySampledHubTotals
public import Oberwolfach.OrderedOrdinarySpokeTarget

@[expose] public section
/-! The full unmarked wheel weight at a hub has the manuscript's
frequency-normalized expectation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordered_ordinary_seed_hub_expectation
    (P:SimpleGraph V) (π:Equiv.Perm V) (p k:ℝ) (hp:0<p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j ≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (m:ℕ) (hm:2≤m) (g:Γ) (j:Color) (D:ℝ) (hD:0<D) (hspos:∀u,0<s u j)
    (η:U→ℝ) (weight:(Fin (m+1)→V)→ℝ)
    (hsupport:∀W:OrderedOrdinaryWheel (U:=U) π (3*d) (m+1),weight W.1.val≠0→
      ∀i:Fin (m+1),P.Adj (W.1.val i) (W.1.val (cycleNext i))) (u:U):
    let seed:=fun W:OrderedOrdinaryWheel (U:=U) π (3*d) (m+1)=>η W.2*weight W.1.val/
      (((m+1:ℕ):ℝ)*D*p^(m+1)*(s W.2 j)^m);
    (FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk hsum d hd q hq hQ s hs hS)).expectation
      (orderedOrdinarySampledHubTotal P π d m seed g j u)=
    (η u*s u j/(((m+1:ℕ):ℝ)*D))*
      ∑C:{C:Fin (m+1)→V // PermutationSeparated π (3*d) C},weight C.val :=by
  intro seed
  rw [ordered_ordinary_sampled_hub_total_expectation P π p k hp.le hk hsum d hd q hq hQ s hs hS hnoshort m hm seed g j u]
  have hterm (W:OrderedOrdinaryWheel (U:=U) π (3*d) (m+1)):
      orderedOrdinaryHubWeight seed u W *
        ∏a∈orderedOrdinaryResources W,rawMarkedWheelMarginal P π d p k q s g j (orderedOrdinaryResourceEmbedding a)=
      if W.2=u then (η u*s u j/(((m+1:ℕ):ℝ)*D))*weight W.1.val else 0:=by
    by_cases hhub:W.2=u
    · simp only [orderedOrdinaryHubWeight,hhub,ite_true]
      by_cases hw:weight W.1.val=0
      · simp [seed,hw]
      · have hprod:=Finset.prod_congr rfl (fun a (ha:a∈orderedOrdinaryResources W)=>
          orderedOrdinary_marginal_on_candidate P d (by omega) W (hsupport W hw) p k q s g j a ha)
        rw [hprod,orderedOrdinaryResources_constant_product W (by omega) p (s W.2 j)]
        dsimp [seed]
        rw [hhub]
        have hr0:(((m+1:ℕ):ℝ))≠0:=by exact_mod_cast (show m+1≠0 by omega)
        have hs0:s u j≠0:=ne_of_gt (hspos u)
        rw [pow_succ]
        field_simp [hr0,hD.ne',hp.ne',hs0]
        <;> ring
    · simp [orderedOrdinaryHubWeight,hhub]
  simp_rw [hterm]
  change (∑x:({C:Fin (m+1)→V // PermutationSeparated π (3*d) C}×U),
    if x.2=u then (η u*s u j/(((m+1:ℕ):ℝ)*D))*weight x.1.val else 0)=_
  rw [Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C _
  rw [Finset.sum_eq_single u]
  · simp
  · intro v _ hv
    simp [hv]
  · simp

theorem ordered_ordinary_seed_hub_target
    (P:SimpleGraph V) (π:Equiv.Perm V) (p k:ℝ) (hp:0<p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j ≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (m:ℕ) (hm:2≤m) (g:Γ) (j:Color) (D τ:ℝ) (hD:0<D) (hspos:∀u,0<s u j)
    (η:U→ℝ) (hη:∀u,0≤η u) (weight:(Fin (m+1)→V)→ℝ)
    (hsupport:∀W:OrderedOrdinaryWheel (U:=U) π (3*d) (m+1),weight W.1.val≠0→
      ∀i:Fin (m+1),P.Adj (W.1.val i) (W.1.val (cycleNext i)))
    (hpos:∀v:V,∀i:Fin (m+1),(1-τ)*D≤(∑C:{C:Fin (m+1)→V // PermutationSeparated π (3*d) C},if C.val i=v then weight C.val else 0) ∧
      (∑C:{C:Fin (m+1)→V // PermutationSeparated π (3*d) C},if C.val i=v then weight C.val else 0)≤(1+τ)*D) (u:U):
    let seed:=fun W:OrderedOrdinaryWheel (U:=U) π (3*d) (m+1)=>η W.2*weight W.1.val/
      (((m+1:ℕ):ℝ)*D*p^(m+1)*(s W.2 j)^m)
    let mean:=(FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk hsum d hd q hq hQ s hs hS)).expectation
      (orderedOrdinarySampledHubTotal P π d m seed g j u);
    (1-τ)*(η u*s u j)*(Fintype.card V:ℝ)/((m+1:ℕ):ℝ)≤mean ∧
      mean≤(1+τ)*(η u*s u j)*(Fintype.card V:ℝ)/((m+1:ℕ):ℝ) :=by
  intro seed mean
  let T:ℝ:=∑C:{C:Fin (m+1)→V // PermutationSeparated π (3*d) C},weight C.val
  let i:Fin (m+1):=⟨0,by omega⟩
  have hsumT:(∑v:V,∑C:{C:Fin (m+1)→V // PermutationSeparated π (3*d) C},if C.val i=v then weight C.val else 0)=T:=by
    rw [Finset.sum_comm]
    dsimp [T]
    apply Finset.sum_congr rfl
    intro C _
    simp
  have hlo:(Fintype.card V:ℝ)*((1-τ)*D)≤T:=by
    have hh:∑_v:V,(1-τ)*D≤∑v:V,∑C:{C:Fin (m+1)→V // PermutationSeparated π (3*d) C},if C.val i=v then weight C.val else 0:=
      Finset.sum_le_sum (fun v _=>(hpos v i).1)
    simpa [hsumT] using hh
  have hhi:T≤(Fintype.card V:ℝ)*((1+τ)*D):=by
    have hh:(∑v:V,∑C:{C:Fin (m+1)→V // PermutationSeparated π (3*d) C},if C.val i=v then weight C.val else 0)≤∑_v:V,(1+τ)*D:=
      Finset.sum_le_sum (fun v _=>(hpos v i).2)
    simpa [hsumT] using hh
  have heq:mean=(η u*s u j/(((m+1:ℕ):ℝ)*D))*T:=by
    exact ordered_ordinary_seed_hub_expectation P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort m hm g j D hD hspos η weight hsupport u
  have hfac:0≤η u*s u j/(((m+1:ℕ):ℝ)*D):=div_nonneg (mul_nonneg (hη u) (hs u j)) (by positivity)
  have hl:=mul_le_mul_of_nonneg_left hlo hfac
  have hh:=mul_le_mul_of_nonneg_left hhi hfac
  rw [←heq] at hl hh
  have hr:(((m+1:ℕ):ℝ))≠0:=by exact_mod_cast (show m+1≠0 by omega)
  constructor
  · convert hl using 1 <;> field_simp [hr,hD.ne'] <;> ring
  · convert hh using 1 <;> field_simp [hr,hD.ne'] <;> ring
end Oberwolfach
