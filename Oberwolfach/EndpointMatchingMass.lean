module

public import Oberwolfach.EndpointMatchingTargets
public import Oberwolfach.WeightedGraphHandshake

@[expose] public section

/-! Identify the endpoint total with the original sum over unordered
eligible edges. The normalizing factor one half is justified by incidence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def endpointEligibleGraph (G F : SimpleGraph V) (P : Finset V) (x : V) : SimpleGraph V where
  Adj v w := v∈P ∧ w∈P ∧ ¬F.Adj x v ∧ ¬F.Adj x w ∧ G.Adj v w ∧ ¬F.Adj v w
  symm:=⟨by intro v w h;exact ⟨h.2.1,h.1,h.2.2.2.1,h.2.2.1,h.2.2.2.2.1.symm,fun hf=>h.2.2.2.2.2 hf.symm⟩⟩
  loopless:=⟨by intro v h;exact h.2.2.2.2.1.ne rfl⟩

theorem endpoint_eligible_ordered_mass (G F : SimpleGraph V) (P : Finset V) (x : V)
    (weight : Sym2 V→ℝ) (hzero : ∀ v∈P,∀ w∈P,¬G.Adj v w → weight s(v,w)=0) :
    endpointEligibleOrderedMass F P x (fun v w=>weight s(v,w))=
      2*∑ e∈(endpointEligibleGraph G F P x).edgeFinset,weight e := by
  rw [←weighted_graph_handshake]
  unfold endpointEligibleOrderedMass endpointEligibleRowWeight
  have expand (P : Finset V) (f : V→ℝ) : (∑ v∈P,f v)=∑ v,if v∈P then f v else 0 := by simp
  rw [expand]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hvP:v∈P <;> by_cases hxv:F.Adj x v
  · simp [hvP,hxv,endpointEligibleGraph]
  · simp only [hvP,ite_true,hxv,not_false_eq_true]
    rw [expand]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hwP:w∈P <;> by_cases hxw:F.Adj x w <;> by_cases hvw:F.Adj v w <;>
      by_cases hg:G.Adj v w <;> simp_all [endpointEligibleGraph]
  · simp [hvP,endpointEligibleGraph]
  · simp [hvP,endpointEligibleGraph]

theorem endpoint_unordered_matching_mass_error (G F : SimpleGraph V) (P : Finset V) (x : V)
    (weight : Sym2 V→ℝ) (a C L : ℝ) (ha : 0<a) (hC : 0≤C)
    (hPa : (P.card:ℝ)≤a) (hF : ∀ u,(F.degree u:ℝ)≤L)
    (hweight : ∀ v∈P,∀ w∈P,0≤weight s(v,w) ∧ weight s(v,w)≤C/a)
    (hsum : ∀ v∈P,∑ w∈P,weight s(v,w)=1)
    (hzero : ∀ v∈P,∀ w∈P,¬G.Adj v w → weight s(v,w)=0) :
    |(∑ e∈(endpointEligibleGraph G F P x).edgeFinset,weight e)-(P.card:ℝ)/2|≤(1+2*C)*L/2 := by
  have hh:=endpoint_matching_total_target F P x (fun v w=>weight s(v,w)) a C L ha hC hPa hF hweight hsum
  rw [endpoint_eligible_ordered_mass G F P x weight hzero] at hh
  convert hh using 1 <;> ring

end Oberwolfach
