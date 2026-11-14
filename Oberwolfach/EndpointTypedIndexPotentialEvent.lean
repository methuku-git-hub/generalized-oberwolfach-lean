module

public import Oberwolfach.EndpointTypedIndexPotentialTail
public import Oberwolfach.EndpointPotentialFailure
public import Oberwolfach.CommonEvents

@[expose] public section

/-! Uniform concentration of the index potential over a fixed family of
roots and hubs under one original raw sampling event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem endpoint_typed_index_variance_bound (a b ω p C S:ℝ)
    (ha:0<a) (hω:0<ω) (hp:0<p) (hC:0<C) (hS:0<S) (hb:ω*a≤b):
    let M:=C/(a*b*p^5)
    S^2*((M*(3*a))*5*(M*a^2))≤(S^2*15*(C/(ω*p^5))^2)/a:=by
  dsimp only
  have hb0:0<b:=(mul_pos hω ha).trans_le hb
  have hm:C/(a*b*p^5)≤(C/(ω*p^5))/a^2:=by
    calc
      _≤C/(a*(ω*a)*p^5):=div_le_div_of_nonneg_left hC.le (by positivity) (by gcongr)
      _=_:=by field_simp <;> ring
  calc
    _≤S^2*((((C/(ω*p^5))/a^2)*(3*a))*5*(((C/(ω*p^5))/a^2)*a^2)):=by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg S)
      exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm (by positivity)) (by norm_num))
        (mul_le_mul_of_nonneg_right hm (by positivity)) (by positivity) (by positivity)
    _=_:=by field_simp <;> ring

theorem endpoint_typed_index_potential_common_event (K ω p₀ C t:ℝ)
    (hK:1≤K) (hω:0<ω) (hp₀:0<p₀) (hC:0<C) (ht:0<t) (d q₀:ℕ) (hd:2≤d):
    ∃ N:ℕ,∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U],
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V) (A:Finset V) (B:Finset U) (X:Finset V),N≤A.card →
      (Fintype.card V:ℝ)≤K*A.card → (Fintype.card U:ℝ)≤K*A.card → ω*A.card≤(B.card:ℝ) → permutationConflictGraph π (3*d)≤F →
      (∀ z l,0<l→l<2*d+1→(π^l) z≠z) →
    ∀ (pR pH:ℝ) (hpR0:p₀≤pR) (hpR1:pR≤1) (hpH0:p₀≤pH)
      (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j:Color),(∀ u∈B,s u j=pH) →
    ∀ (weight:V→Sym2 V→ℝ),
      (∀ x∈X,∀ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet,
        0≤weight x e∧weight x e≤C/A.card) →
    1-1/(A.card:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hp₀.le.trans hpR0) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ x∈X,∀ u∈B,
          |rawOrdinaryPatternSum P π d
            (fun e:↥(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset=>endpointIndexResources x u e.val)
            (fun e=>weight x e.val/(B.card*pR^2*pH^3)) j σ-
            pR/(B.card*pH)*(∑ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,weight x e)|<t):=by
  have hK0:0<K:=lt_of_lt_of_le zero_lt_one hK
  let Z:ℝ:=(4*(d:ℝ)+3)^2*15*(C/(ω*p₀^5))^2
  have hZ:0<Z:=by dsimp [Z];positivity
  obtain ⟨N,hN⟩:=constant_deviation_failure_eventually_small (K^2) Z t hZ ht 2 q₀
  refine ⟨max N 1,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P F π A B X hn hV hU hB hF hnoshort pR pH hpR0 hpR1 hpH0 q hq hQ s hs hS j hj weight hw
  have ha:0<A.card:=by omega
  have ha0:(0:ℝ)<A.card:=Nat.cast_pos.mpr ha
  have hb0:(0:ℝ)<B.card:=(mul_pos hω ha0).trans_le hB
  have hb:0<B.card:=Nat.cast_pos.mp hb0
  let I:={p:V×U//p.1∈X∧p.2∈B}
  let μ:=FiniteLaw.pi (rawWheelLaw (fun _:Sym2 V=>pR) (fun _=>hp₀.le.trans hpR0) (fun _=>hpR1) d hd q hq hQ s hs hS)
  let val:=fun (i:I) (σ:RawWheelOutcome V U Γ Color)=>
    |rawOrdinaryPatternSum P π d
      (fun e:↥(endpointEligibleGraph P F (A∩P.neighborFinset i.val.1) i.val.1).edgeFinset=>endpointIndexResources i.val.1 i.val.2 e.val)
      (fun e=>weight i.val.1 e.val/(B.card*pR^2*pH^3)) j σ-
      pR/(B.card*pH)*(∑ e∈(endpointEligibleGraph P F (A∩P.neighborFinset i.val.1) i.val.1).edgeFinset,weight i.val.1 e)|
  let err:=2*Real.exp (-2*t^2/(Z/A.card))
  have htail (i:I):μ.probability (fun σ=>t≤val i σ)≤err:=by
    have hh:=raw_typed_endpoint_index_potential_tail P F A B i.val.1 i.val.2 ha hb i.property.2
      π d hd hF hnoshort p₀ pR pH C hp₀ hpR0 hpR1 hpH0 hC q hq hQ s hs hS j (hj i.val.2 i.property.2)
      (weight i.val.1) (hw i.val.1 i.property.1) t ht
    apply hh.trans
    apply endpoint_tail_variance_mono t
    · positivity
    · exact endpoint_typed_index_variance_bound _ _ ω p₀ C _ ha0 hω hp₀ hC (by positivity) hB
  have hc:(Fintype.card I:ℝ)≤K^2*(A.card:ℝ)^2:=by
    have hc':Fintype.card I≤Fintype.card (V×U):=Fintype.card_subtype_le _
    have hh:(Fintype.card I:ℝ)≤(Fintype.card V:ℝ)*Fintype.card U:=by
      exact_mod_cast (by simpa only [Fintype.card_prod] using hc')
    calc
      _ ≤ (Fintype.card V:ℝ)*Fintype.card U := hh
      _ ≤ (K*A.card)*(K*A.card) := mul_le_mul hV hU (by positivity) (by positivity)
      _ = K^2*(A.card:ℝ)^2 := by ring
  have hf:=hN A.card (by omega) (Fintype.card I) (by positivity) hc
  have hh:=finiteLaw_common_event_lower μ Finset.univ (fun i σ=>t≤val i σ) (fun _=>err) (fun i _=>htail i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies] at hh
  apply ((sub_le_sub_left hf 1).trans hh).trans
  apply finiteLaw_probability_mono
  intro σ hσ x hx u hu
  exact not_le.mp (hσ ⟨(x,u),hx,hu⟩)

end Oberwolfach
