module

public import Oberwolfach.EndpointIndexResourceCounts
public import Oberwolfach.EndpointIndexPatternIdentity

@[expose] public section

/-! Original-law concentration for the hub-root potential, omitting the
root spoke and retaining the fixed unordered eligible-edge weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U]

theorem endpoint_typed_index_pattern_mean (P F:SimpleGraph V) (A:Finset V) (B:Finset U) (x:V)
    (weight:Sym2 V→ℝ) (pR pH:ℝ) (hpR:0<pR) (hpH:0<pH) (hB:0<B.card):
    pR^3*pH^2*(∑ e:↥(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,
      weight e.val/(B.card*pR^2*pH^3))=
      pR/(B.card*pH)*(∑ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,weight e):=by
  have hs:(∑ e:↥(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,
      weight e.val/(B.card*pR^2*pH^3))=
      ∑ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,weight e/(B.card*pR^2*pH^3):=by
    exact Finset.sum_coe_sort _ (fun e=>weight e/(B.card*pR^2*pH^3))
  rw [hs,←Finset.sum_div]
  have hb:(0:ℝ)<B.card:=Nat.cast_pos.mpr hB
  field_simp <;> ring


theorem raw_typed_endpoint_index_potential_tail (P F:SimpleGraph V) (A:Finset V) (B:Finset U) (x:V) (u:U)
    (hA:0<A.card) (hB:0<B.card) (hu:u∈B)
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d) (hF:permutationConflictGraph π (3*d)≤F)
    (hnoshort:∀ z l,0<l→l<2*d+1→(π^l) z≠z)
    (p₀ pR pH C:ℝ) (hp₀:0<p₀) (hpR0:p₀≤pR) (hpR1:pR≤1) (hpH0:p₀≤pH) (hC:0<C)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
    (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (j:Color) (hj:s u j=pH)
    (weight:Sym2 V→ℝ)
    (hw:∀ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet,
      0≤weight e∧weight e≤C/A.card)
    (t:ℝ) (ht:0<t):
    let M:=C/((A.card:ℝ)*B.card*p₀^5)
    (FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hp₀.le.trans hpR0) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
      (fun σ=>t≤|rawOrdinaryPatternSum P π d
        (fun e:↥(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset=>endpointIndexResources x u e.val)
        (fun e=>weight e.val/(B.card*pR^2*pH^3)) j σ-
        pR/(B.card*pH)*(∑ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,weight e)|)≤
      2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((M*(3*A.card))*5*(M*(A.card:ℝ)^2)))):=by
  dsimp only
  let E:=endpointEligibleGraph P F (A∩P.neighborFinset x) x
  let D:ℝ:=B.card*pR^2*pH^3
  let M:ℝ:=C/((A.card:ℝ)*B.card*p₀^5)
  have ha:(0:ℝ)<A.card:=Nat.cast_pos.mpr hA
  have hb:(0:ℝ)<B.card:=Nat.cast_pos.mpr hB
  have hpR:0<pR:=hp₀.trans_le hpR0
  have hpH:0<pH:=hp₀.trans_le hpH0
  have hD:0<D:=by dsimp [D];positivity
  have hM:0<M:=by dsimp [M];positivity
  have hpow:p₀^5≤pR^2*pH^3:=by
    have hh:=mul_le_mul (pow_le_pow_left₀ hp₀.le hpR0 2) (pow_le_pow_left₀ hp₀.le hpH0 3)
      (pow_nonneg hp₀.le 3) (pow_nonneg hpR.le 2)
    nlinarith only [hh]
  let w:↥E.edgeFinset→ℝ:=fun e=>weight e.val/D
  have hw' (e:↥E.edgeFinset):0≤w e∧w e≤M:=by
    have hwe:=hw e.val (SimpleGraph.mem_edgeFinset.mp e.property)
    refine ⟨div_nonneg hwe.1 hD.le,?_⟩
    calc
      w e≤(C/A.card)/D:=div_le_div_of_nonneg_right hwe.2 hD.le
      _≤(C/A.card)/(B.card*p₀^5):=div_le_div_of_nonneg_left (by positivity)
        (by positivity) (by dsimp [D];simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpow hb.le)
      _=M:=by dsimp [M];field_simp <;> ring
  have hvert:∀ e∈E.edgeSet,∀ v∈e,v∈A:=endpoint_eligible_edge_vertices P F A x
  have hsep (e:↥E.edgeFinset):∀ v∈e.val,∀ w∈e.val,¬F.Adj v w:=by
    obtain ⟨e,he⟩:=e
    induction e using Sym2.ind with
    | _ v w=>
      have hh:=SimpleGraph.mem_edgeFinset.mp he
      intro a ha b hb
      rcases Sym2.mem_iff.mp ha with rfl|rfl <;> rcases Sym2.mem_iff.mp hb with rfl|rfl
      · exact F.loopless.irrefl _
      · exact hh.2.2.2.2.2
      · exact fun h=>hh.2.2.2.2.2 h.symm
      · exact F.loopless.irrefl _
  have htotal:=endpointIndexCandidates_weight_bounds E A hvert hA x u w M hM.le hw'
  let R:=fun e:↥E.edgeFinset=>endpointIndexResources x u e.val
  have hh:=rawOrdinaryPatternSum_tail P π (fun _=>pR) (fun _=>hp₀.le.trans hpR0) (fun _=>hpR1)
    d hd q hq hQ s hs hS hnoshort R w (fun e=>(hw' e).1)
    (fun e a ha b hb hne=>endpointIndexResources_disjoint π d F hF x u e.val (hsep e) a b ha hb hne) j
    (M*(3*A.card)) 5 (M*(A.card:ℝ)^2) (by positivity) (by norm_num) (by positivity)
    (fun e=>by exact_mod_cast endpointIndexResources_card x u e.val) htotal.1 htotal.2 t ht
  have htarget (e:↥E.edgeFinset):
      (∏ f∈R e,rawWheelMarginal P (fun _=>pR) s j f)=pR^3*pH^2:=by
    obtain ⟨e,he⟩:=e
    induction e using Sym2.ind with
    | _ v w=>
      have hh:=SimpleGraph.mem_edgeFinset.mp he
      exact endpointIndexResources_target P s j pR pH x v w u
        ((P.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hh.1).2)
        ((P.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hh.2.1).2) hh.2.2.2.2.1 hj
  have htarg:(∑ e,w e*∏ f∈R e,rawWheelMarginal P (fun _=>pR) s j f)=pR^3*pH^2*(∑ e,w e):=by
    simp_rw [htarget]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _;ring
  have hm:pR^3*pH^2*(∑ e,w e)=pR/(B.card*pH)*(∑ e∈E.edgeFinset,weight e):=
    endpoint_typed_index_pattern_mean P F A B x weight pR pH hpR hpH hB
  simpa only [htarg,hm] using hh

end Oberwolfach
