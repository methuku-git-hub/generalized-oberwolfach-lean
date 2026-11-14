module

public import Oberwolfach.EndpointRowPotentialTail
public import Oberwolfach.EndpointPotentialFailure
public import Oberwolfach.CommonEvents

@[expose] public section

/-! One original-law event controls the endpoint row potentials for all
fixed roots and their eligible neighbours. The parent weights are supplied
before the random outcome; neither the domains nor weights are resampled. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem endpoint_row_potential_common_event (K ω p₀ C t:ℝ)
    (hK:1≤K) (hω:0<ω) (hp₀:0<p₀) (hC:0<C) (ht:0<t) (d q₀:ℕ) (hd:2≤d):
    ∃ N:ℕ,∀ (V Γ Color:Type) [Fintype V] [Fintype Γ] [Fintype Color] [DecidableEq V],
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V) (A B X:Finset V),N≤A.card →
      (Fintype.card V:ℝ)≤K*A.card → ω*A.card≤(B.card:ℝ) →
      (∀ x∈X,Disjoint (insert x A) B) → permutationConflictGraph π (3*d)≤F →
      (∀ z l,0<l→l<2*d+1→(π^l) z≠z) →
    ∀ (pR pH:ℝ) (hpR0:p₀≤pR) (hpR1:pR≤1) (hpH0:p₀≤pH)
      (q:V→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:V→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j:Color),(∀ u∈B,s u j=pH) →
    ∀ (weight:V→Sym2 V→ℝ),
      (∀ x∈X,∀ v∈A∩P.neighborFinset x,∀ w∈A∩P.neighborFinset x,
        0≤weight x s(v,w)∧weight x s(v,w)≤C/A.card) →
      (∀ x∈X,∀ v∈A∩P.neighborFinset x,∀ w∈A∩P.neighborFinset x,
        ¬P.Adj v w→weight x s(v,w)=0) →
    1-1/(A.card:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hp₀.le.trans hpR0) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ x∈X,∀ (hAB:Disjoint (insert x A) B),
          ∀ v∈common A {x} (fun z=>(P\F).neighborFinset z),
          |endpointRowPotential P (rawWheelGraph P σ)
            (bipartiteRelationGraph (insert x A) B hAB (rawWheelSpokes π d σ j)) F A B x v (weight x) (B.card*pR^2*pH^3)-
            endpointEligibleRowWeight F (A∩P.neighborFinset x) x v (fun v w=>weight x s(v,w))|<t):=by
  have hK0:0<K:=lt_of_lt_of_le zero_lt_one hK
  let Z:ℝ:=(4*(d:ℝ)+3)^2*5*(C/(ω*p₀^5))^2*(2*K+1)*K
  have hZ:0<Z:=by dsimp [Z];positivity
  obtain ⟨N,hN⟩:=constant_deviation_failure_eventually_small (K^2) Z t hZ ht 2 q₀
  refine ⟨max N 1,?_⟩
  intro V Γ Color _ _ _ _ P F π A B X hn hV hB hAB hF hnoshort pR pH hpR0 hpR1 hpH0 q hq hQ s hs hS j hj weight hw hzero
  have ha:0<A.card:=by omega
  have ha0:(0:ℝ)<A.card:=Nat.cast_pos.mpr ha
  have hb0:(0:ℝ)<B.card:=(mul_pos hω ha0).trans_le hB
  have hb:0<B.card:=Nat.cast_pos.mp hb0
  have hb':(B.card:ℝ)≤K*A.card:=(Nat.cast_le.mpr (Finset.card_le_univ B)).trans hV
  let I:={p:V×V//p.1∈X∧p.2∈common A {p.1} (fun z=>(P\F).neighborFinset z)}
  let μ:=FiniteLaw.pi (rawWheelLaw (fun _:Sym2 V=>pR) (fun _=>hp₀.le.trans hpR0) (fun _=>hpR1) d hd q hq hQ s hs hS)
  let val:=fun (i:I) (σ:RawWheelOutcome V V Γ Color)=>
    |endpointRowPotential P (rawWheelGraph P σ)
      (bipartiteRelationGraph (insert i.val.1 A) B (hAB i.val.1 i.property.1) (rawWheelSpokes π d σ j))
      F A B i.val.1 i.val.2 (weight i.val.1) (B.card*pR^2*pH^3)-
      endpointEligibleRowWeight F (A∩P.neighborFinset i.val.1) i.val.1 i.val.2 (fun v w=>weight i.val.1 s(v,w))|
  let err:=2*Real.exp (-2*t^2/(Z/A.card))
  have htail (i:I):μ.probability (fun σ=>t≤val i σ)≤err:=by
    have hv' : i.val.2∈A∧(P\F).Adj i.val.1 i.val.2:=by
      simpa only [mem_common_iff,Finset.mem_singleton,forall_eq,SimpleGraph.mem_neighborFinset] using i.property.2
    have hvPx:i.val.2∈A∩P.neighborFinset i.val.1:=Finset.mem_inter.mpr ⟨hv'.1,(P.mem_neighborFinset _ _).mpr hv'.2.1⟩
    have hh:=raw_endpoint_row_potential_tail P F A B i.val.1 i.val.2 ha hb (hAB i.val.1 i.property.1) i.property.2
      π d hd hF hnoshort p₀ pR pH C hp₀ hpR0 hpR1 hpH0 hC q hq hQ s hs hS j hj (weight i.val.1)
      (hw i.val.1 i.property.1 i.val.2 hvPx) (hzero i.val.1 i.property.1 i.val.2 hvPx) t ht
    apply hh.trans
    apply endpoint_tail_variance_mono t
    · positivity
    · exact endpoint_row_variance_bound _ _ K ω p₀ C _ ha0 hω hp₀ hC (by positivity) hB hb'
  have hc:(Fintype.card I:ℝ)≤K^2*(A.card:ℝ)^2:=by
    have hc':Fintype.card I≤Fintype.card (V×V):=Fintype.card_subtype_le _
    have hh:(Fintype.card I:ℝ)≤(Fintype.card V:ℝ)^2:=by
      exact_mod_cast (by simpa only [Fintype.card_prod,pow_two] using hc')
    exact hh.trans (by simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hV 2)
  have hf:=hN A.card (by omega) (Fintype.card I) (by positivity) hc
  have hh:=finiteLaw_common_event_lower μ Finset.univ (fun i σ=>t≤val i σ) (fun _=>err) (fun i _=>htail i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies] at hh
  apply ((sub_le_sub_left hf 1).trans hh).trans
  apply finiteLaw_probability_mono
  intro σ hσ x hx hAB' v hv
  exact not_le.mp (hσ ⟨(x,v),hx,hv⟩)

end Oberwolfach
