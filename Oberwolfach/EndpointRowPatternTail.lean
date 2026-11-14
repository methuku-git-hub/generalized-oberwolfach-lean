module

public import Oberwolfach.EndpointRowResources

@[expose] public section

/-! Concentration for the actual five-resource endpoint row patterns.
The coefficients are fixed before sampling, and the tested root is absent
from every pattern. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

theorem endpointRowCandidates_weight_bounds (E:SimpleGraph V) (A:Finset V) (B:Finset U) (x v:V)
    (w:EndpointRowCandidates E A B v→ℝ) (M:ℝ) (hM:0≤M) (hw:∀ p,0≤w p∧w p≤M):
    (∑ p,w p)≤M*(B.card*A.card) ∧
    ∀ e:Sym2 V⊕(V×U),(∑ p,if e∈endpointRowResources x v p.val.2 p.val.1 then w p else 0)
      ≤M*(2*B.card+A.card):=by
  constructor
  · calc
      _≤∑ _p:EndpointRowCandidates E A B v,M:=Finset.sum_le_sum (fun p _=>(hw p).2)
      _=M*Fintype.card (EndpointRowCandidates E A B v):=by simp [mul_comm]
      _≤_:=mul_le_mul_of_nonneg_left (by exact_mod_cast endpointRowCandidates_card E A B v) hM
  · intro e
    rw [←Finset.sum_filter]
    calc
      _≤∑ p∈Finset.univ.filter (fun p:EndpointRowCandidates E A B v=>e∈endpointRowResources x v p.val.2 p.val.1),M:=
        Finset.sum_le_sum (fun p _=>(hw p).2)
      _=M*(Finset.univ.filter (fun p:EndpointRowCandidates E A B v=>e∈endpointRowResources x v p.val.2 p.val.1)).card:=by simp [mul_comm]
      _≤_:=mul_le_mul_of_nonneg_left (by exact_mod_cast endpointRowCandidates_incidence E A B x v e) hM

theorem raw_endpoint_row_pattern_tail (P E F:SimpleGraph V) (A:Finset V) (B:Finset U) (x v:V)
    (hA:0<A.card) (hB:0<B.card) (hxv:x≠v)
    (hE:∀ w,E.Adj v w→P.Adj x w∧P.Adj v w∧
      ∀ a∈({x,v,w}:Finset V),∀ b∈({x,v,w}:Finset V),¬F.Adj a b)
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d) (hF:permutationConflictGraph π (3*d)≤F)
    (hnoshort:∀ z l,0<l→l<2*d+1→(π^l) z≠z)
    (pR pH:ℝ) (hpR:0≤pR) (hpR1:pR≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
    (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (j:Color) (hj:∀ u∈B,s u j=pH)
    (w:EndpointRowCandidates E A B v→ℝ) (M:ℝ) (hM:0<M) (hw:∀ p,0≤w p∧w p≤M)
    (t:ℝ) (ht:0<t):
    (FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
      (fun σ=>t≤|rawOrdinaryPatternSum P π d (fun p:EndpointRowCandidates E A B v=>endpointRowResources x v p.val.2 p.val.1) w j σ-
        pR^2*pH^3*(∑ p,w p)|)≤
      2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((M*(2*B.card+A.card))*5*(M*(B.card*A.card))))):=by
  let R:=fun p:EndpointRowCandidates E A B v=>endpointRowResources x v p.val.2 p.val.1
  have hsep (p:EndpointRowCandidates E A B v):= (hE p.val.2 p.property.2.2).2.2
  have htotal:=endpointRowCandidates_weight_bounds E A B x v w M hM.le hw
  have ha:(0:ℝ)<A.card:=Nat.cast_pos.mpr hA
  have hb:(0:ℝ)<B.card:=Nat.cast_pos.mpr hB
  have hh:=rawOrdinaryPatternSum_tail P π (fun _=>pR) (fun _=>hpR) (fun _=>hpR1)
    d hd q hq hQ s hs hS hnoshort R w (fun p=>(hw p).1)
    (fun p a ha b hb hne=>endpointRowResources_disjoint π d F hF x v p.val.2 p.val.1 (hsep p) a b ha hb hne) j
    (M*(2*B.card+A.card)) 5 (M*(B.card*A.card)) (by positivity) (by norm_num) (by positivity)
    (fun p=>by exact_mod_cast endpointRowResources_card x v p.val.2 p.val.1) htotal.1 htotal.2 t ht
  have he:(∑ p,w p*∏ e∈R p,rawWheelMarginal P (fun _=>pR) s j e)=pR^2*pH^3*(∑ p,w p):=by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    have ht:=endpointRowResources_target P s j pR pH x v p.val.2 p.val.1 hxv
      (hE p.val.2 p.property.2.2).1.ne (hE p.val.2 p.property.2.2).2.1.ne
      (hE p.val.2 p.property.2.2).1 (hE p.val.2 p.property.2.2).2.1 (hj p.val.1 p.property.1)
    change _* (∏ e∈endpointRowResources x v p.val.2 p.val.1,_) =_
    rw [ht];ring
  simpa only [he] using hh

end Oberwolfach
