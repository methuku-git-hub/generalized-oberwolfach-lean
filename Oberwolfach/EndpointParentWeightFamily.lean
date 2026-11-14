module

public import Oberwolfach.EndpointParentWeights

@[expose] public section

/-! Choose one family of parent fractional matchings before any sampling.
Each weight function is independent of both the conflict graph and outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem endpoint_parent_weight_family (P:SimpleGraph V) (A X:Finset V) (hn:32≤A.card)
    (hdeg:∀ x∈X,∀ v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ)):
    ∃ weight:V→Sym2 V→ℝ,∀ x∈X,
      (∀ v∈A∩P.neighborFinset x,∀ w∈A∩P.neighborFinset x,
        0≤weight x s(v,w)∧weight x s(v,w)≤40/A.card) ∧
      (∀ v∈A∩P.neighborFinset x,∑ w∈A∩P.neighborFinset x,weight x s(v,w)=1) ∧
      (∀ v w,¬P.Adj v w→weight x s(v,w)=0) ∧
      (∀ F:SimpleGraph V,∀ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet,
        (1/30:ℝ)/A.card≤weight x e∧weight x e≤40/A.card):=by
  have hex:=fun x:↥X=>endpoint_parent_matching_exists P A x.val hn (hdeg x.val x.property)
  choose w hw using hex
  let weight:V→Sym2 V→ℝ:=fun x=>if hx:x∈X then w ⟨x,hx⟩ else fun _=>0
  refine ⟨weight,?_⟩
  intro x hx
  simpa only [weight,dif_pos hx] using hw ⟨x,hx⟩

end Oberwolfach
