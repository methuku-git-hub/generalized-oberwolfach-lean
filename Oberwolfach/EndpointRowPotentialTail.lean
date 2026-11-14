module

public import Oberwolfach.EndpointRowPatternTail
public import Oberwolfach.EndpointRowPatternIdentity
public import Oberwolfach.EndpointRowPatternMean

@[expose] public section

/-! A tail estimate for the manuscript's original endpoint row potential,
with its fixed parent weights and root-omitted target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V Γ Color:Type} [Fintype V] [Fintype Γ] [Fintype Color] [DecidableEq V]

theorem raw_endpoint_row_potential_tail (P F:SimpleGraph V) (A B:Finset V) (x v:V)
    (hA:0<A.card) (hB:0<B.card) (hAB:Disjoint (insert x A) B)
    (hv:v∈common A {x} (fun z=>(P\F).neighborFinset z))
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d) (hF:permutationConflictGraph π (3*d)≤F)
    (hnoshort:∀ z l,0<l→l<2*d+1→(π^l) z≠z)
    (p₀ pR pH C:ℝ) (hp₀:0<p₀) (hpR0:p₀≤pR) (hpR1:pR≤1) (hpH0:p₀≤pH) (hC:0<C)
    (q:V→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:V→Color→ℝ) (hs:∀ u j,0≤s u j)
    (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (j:Color) (hj:∀ u∈B,s u j=pH)
    (weight:Sym2 V→ℝ)
    (hw:∀ w∈A∩P.neighborFinset x,0≤weight s(v,w)∧weight s(v,w)≤C/A.card)
    (hzero:∀ w∈A∩P.neighborFinset x,¬P.Adj v w→weight s(v,w)=0)
    (t:ℝ) (ht:0<t):
    let M:=C/((A.card:ℝ)*B.card*p₀^5)
    (FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hp₀.le.trans hpR0) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
      (fun σ=>t≤|endpointRowPotential P (rawWheelGraph P σ)
        (bipartiteRelationGraph (insert x A) B hAB (rawWheelSpokes π d σ j)) F A B x v weight (B.card*pR^2*pH^3)-
        endpointEligibleRowWeight F (A∩P.neighborFinset x) x v (fun v w=>weight s(v,w))|)≤
      2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((M*(2*B.card+A.card))*5*(M*(B.card*A.card))))):=by
  dsimp only
  have hv' : v∈A ∧ (P\F).Adj x v := by
    simpa only [mem_common_iff,Finset.mem_singleton,forall_eq,
      SimpleGraph.mem_neighborFinset] using hv
  have hPv:P.Adj x v:=hv'.2.1
  have hFx:¬F.Adj x v:=hv'.2.2
  have hvPx:v∈A∩P.neighborFinset x:=Finset.mem_inter.mpr ⟨hv'.1,(P.mem_neighborFinset _ _).mpr hPv⟩
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
  let w:EndpointRowCandidates E A B v→ℝ:=fun z=>weight s(v,z.val.2)/D
  have hw' (z:EndpointRowCandidates E A B v):0≤w z∧w z≤M:=by
    have hwz:=hw z.val.2 z.property.2.2.2.1
    refine ⟨div_nonneg hwz.1 hD.le,?_⟩
    calc
      w z≤(C/A.card)/D:=div_le_div_of_nonneg_right hwz.2 hD.le
      _≤(C/A.card)/(B.card*p₀^5):=div_le_div_of_nonneg_left (by positivity)
        (by positivity) (by dsimp [D];simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpow hb.le)
      _=M:=by dsimp [M];field_simp <;> ring
  have hE (z:V) (hz:E.Adj v z):P.Adj x z∧P.Adj v z∧
      ∀ a∈({x,v,z}:Finset V),∀ b∈({x,v,z}:Finset V),¬F.Adj a b:=by
    have hPz:P.Adj x z:=(P.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hz.2.1).2
    refine ⟨hPz,hz.2.2.2.2.1,?_⟩
    intro a ha b hb
    have hxz:=hz.2.2.2.1
    have hvz:=hz.2.2.2.2.2
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl <;>
      first | exact F.loopless.irrefl _ | exact hFx | exact hxz | exact hvz |
        exact fun h=>hFx h.symm | exact fun h=>hxz h.symm | exact fun h=>hvz h.symm
  have hh:=raw_endpoint_row_pattern_tail P E F A B x v hA hB hPv.ne hE π d hd hF hnoshort
    pR pH hpR.le hpR1 q hq hQ s hs hS j hj w M hM hw' t ht
  have he (σ:RawWheelOutcome V V Γ Color):
      rawOrdinaryPatternSum P π d (fun z:EndpointRowCandidates E A B v=>endpointRowResources x v z.val.2 z.val.1) w j σ=
      endpointRowPotential P (rawWheelGraph P σ)
        (bipartiteRelationGraph (insert x A) B hAB (rawWheelSpokes π d σ j)) F A B x v weight D:=by
    exact endpoint_row_pattern_identity P (rawWheelGraph P σ) F (rawWheelSpokes π d σ j) A B x v hAB hv'.1 weight D
  have hm:pR^2*pH^3*(∑ z,w z)=endpointEligibleRowWeight F (A∩P.neighborFinset x) x v (fun v w=>weight s(v,w)):=
    endpoint_row_pattern_mean P F A B x v hvPx hFx weight hzero pR pH hpR hpH hB
  simpa only [he,hm] using hh

end Oberwolfach
