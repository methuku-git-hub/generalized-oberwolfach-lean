module

public import Oberwolfach.EndpointPhysicalPotentialEvent
public import Oberwolfach.EndpointTypedRowPotentialEvent
public import Oberwolfach.EndpointTypedIndexPotentialEvent

@[expose] public section
/-! Both physical endpoint potentials hold simultaneously under the original
two-domain raw sampling law for fixed parent weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 2048
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem endpoint_physical_potential_common_event (K ω p₀ C t:ℝ)
    (hK:1≤K) (hω:0<ω) (hp₀:0<p₀) (hC:0<C) (ht:0<t) (d q₀:ℕ) (hd:2≤d):
    ∃N:ℕ,∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    ∀(P F:SimpleGraph V) (π:Equiv.Perm V) (A:Finset V) (B:Finset U) (X:Finset V),N≤A.card→
      (Fintype.card V:ℝ)≤K*A.card→(Fintype.card U:ℝ)≤K*A.card→ω*A.card≤(B.card:ℝ)→
      permutationConflictGraph π (3*d)≤F→(∀z l,0<l→l<2*d+1→(π^l) z≠z)→
    ∀(pR pH:ℝ) (hpR0:p₀≤pR) (hpR1:pR≤1) (hpH0:p₀≤pH)
      (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
      (j:Color),(∀u∈B,s u j=pH)→
    ∀(weight:V→Sym2 (V⊕U)→ℝ),
      (∀x∈X,∀v∈A∩P.neighborFinset x,∀w∈A∩P.neighborFinset x,
        0≤weight x s(Sum.inl v,Sum.inl w)∧weight x s(Sum.inl v,Sum.inl w)≤C/A.card)→
      (∀x∈X,∀v∈A∩P.neighborFinset x,∀w∈A∩P.neighborFinset x,
        ¬P.Adj v w→weight x s(Sum.inl v,Sum.inl w)=0)→
      (∀x∈X,∀e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet,
        0≤weight x (Sym2.map Sum.inl e)∧weight x (Sym2.map Sum.inl e)≤C/A.card)→
    1-2/(A.card:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hp₀.le.trans hpR0) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
        (EndpointPhysicalPotentialEvent P F A B X π d j weight pR pH t):=by
  obtain ⟨Nr,hr⟩:=endpoint_typed_row_potential_common_event K ω p₀ C t hK hω hp₀ hC ht d q₀ hd
  obtain ⟨Ni,hi⟩:=endpoint_typed_index_potential_common_event K ω p₀ C t hK hω hp₀ hC ht d q₀ hd
  refine ⟨max Nr Ni,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P F π A B X hn hV hU hB hF hshort
    pR pH hpR0 hpR1 hpH0 q hq hQ s hs hS j hj weight hweight hzero hpositive
  let w:V→Sym2 V→ℝ:=fun x e=>weight x (Sym2.map Sum.inl e)
  have hw:∀x∈X,∀v∈A∩P.neighborFinset x,∀z∈A∩P.neighborFinset x,
      0≤w x s(v,z)∧w x s(v,z)≤C/A.card:=by
    intro x hx v hv z hz
    simpa only [w,Sym2.map_mk] using hweight x hx v hv z hz
  have hz:∀x∈X,∀v∈A∩P.neighborFinset x,∀z∈A∩P.neighborFinset x,
      ¬P.Adj v z→w x s(v,z)=0:=by
    intro x hx v hv z hz h
    simpa only [w,Sym2.map_mk] using hzero x hx v hv z hz h
  have he:∀x∈X,∀e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet,
      0≤w x e∧w x e≤C/A.card:=hpositive
  have hr':=hr V U Γ Color P F π A B X (by omega) hV hU hB hF hshort
    pR pH hpR0 hpR1 hpH0 q hq hQ s hs hS j hj w hw hz
  have hi':=hi V U Γ Color P F π A B X (by omega) hV hU hB hF hshort
    pR pH hpR0 hpR1 hpH0 q hq hQ s hs hS j hj w he
  let μ:=FiniteLaw.pi (rawWheelLaw (fun _:Sym2 V=>pR) (fun _=>hp₀.le.trans hpR0) (fun _=>hpR1) d hd q hq hQ s hs hS)
  have hboth:= (sub_le_sub_right hr' (1/(A.card:ℝ)^q₀)).trans
    (finiteLaw_good_intersection μ _ _ (1/(A.card:ℝ)^q₀) hi')
  have hprob:1-2/(A.card:ℝ)^q₀≤μ.probability
      (fun σ=>
        (∀x∈X,∀v∈common A {x} (fun z=>(P\F).neighborFinset z),
          |rawOrdinaryPatternSum P π d
            (fun z:EndpointRowCandidates (endpointEligibleGraph P F (A∩P.neighborFinset x) x) A B v=>
              endpointRowResources x v z.val.2 z.val.1)
            (fun z=>weight x s(Sum.inl v,Sum.inl z.val.2)/(B.card*pR^2*pH^3)) j σ-
            endpointEligibleRowWeight F (A∩P.neighborFinset x) x v (fun a b=>weight x s(Sum.inl a,Sum.inl b))|<t) ∧
        (∀x∈X,∀u∈B,
          |rawOrdinaryPatternSum P π d
            (fun e:↥(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset=>endpointIndexResources x u e.val)
            (fun e=>weight x (Sym2.map Sum.inl e.val)/(B.card*pR^2*pH^3)) j σ-
            pR/(B.card*pH)*(∑e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,
              weight x (Sym2.map Sum.inl e))|<t)):=by
    convert hboth using 1 <;> try simp only [w,Sym2.map_mk]
    rw [show (2:ℝ)=1+1 by norm_num,add_div]
    ring
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  exact endpoint_typed_potentials_to_physical P F A B X π d j weight pR pH t σ hσ.1 hσ.2
end Oberwolfach
