module

public import Oberwolfach.FractionalResourceMatching
public import Oberwolfach.FiniteCombinedUnitLoad

@[expose] public section
/-! A disjoint union of the actual marked and ordinary candidate families
uses their shared physical resources. No candidates are identified and no
weights are changed. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [Fintype V] [DecidableEq V]
  {E:I→Type} [∀i,Fintype (E i)]

def mixedCandidateResources (R:∀i,E i→Finset V) (e:Σi,E i):Finset V:=R e.1 e.2

def mixedCandidateWeight (w:∀i,E i→ℝ) (e:Σi,E i):ℝ:=w e.1 e.2

theorem mixed_candidate_weighted_degree
    (R:∀i,E i→Finset V) (w:∀i,E i→ℝ) (v:V):
    hypergraphWeightedDegree (mixedCandidateResources R) (mixedCandidateWeight w) v=
      ∑i,hypergraphWeightedDegree (R i) (w i) v:=by
  unfold hypergraphWeightedDegree mixedCandidateResources mixedCandidateWeight
  rw [Fintype.sum_sigma]

theorem mixed_candidate_weighted_codegree
    (R:∀i,E i→Finset V) (w:∀i,E i→ℝ) (u v:V):
    (∑e:Σi,E i,if u∈mixedCandidateResources R e ∧ v∈mixedCandidateResources R e then mixedCandidateWeight w e else 0)=
      ∑i,∑e:E i,if u∈R i e ∧ v∈R i e then w i e else 0:=by
  unfold mixedCandidateResources mixedCandidateWeight
  rw [Fintype.sum_sigma]

theorem mixed_candidate_unit_load_from_components
    (R:∀i,E i→Finset V) (w:∀i,E i→ℝ) (target:I→V→ℝ) (τ t:ℝ)
    (htarget:∀v,∑i,target i v=1)
    (hload:∀i v,|hypergraphWeightedDegree (R i) (w i) v-target i v|≤t+τ*target i v):
    ∀v,|hypergraphWeightedDegree (mixedCandidateResources R) (mixedCandidateWeight w) v-1|≤
      (Fintype.card I:ℝ)*t+τ:=by
  intro v
  rw [mixed_candidate_weighted_degree]
  exact finite_combined_unit_load (fun i=>target i v) (fun i=>hypergraphWeightedDegree (R i) (w i) v)
    τ t (htarget v) (fun i=>hload i v)

theorem mixed_candidate_codegree_from_components
    (R:∀i,E i→Finset V) (w:∀i,E i→ℝ) (K:I→ℝ) (n:ℝ)
    (h:∀i u v,u≠v→(∑e:E i,if u∈R i e ∧ v∈R i e then w i e else 0)≤K i/n):
    ∀u v,u≠v→(∑e:Σi,E i,if u∈mixedCandidateResources R e ∧ v∈mixedCandidateResources R e then mixedCandidateWeight w e else 0)≤
      (∑i,K i)/n:=by
  intro u v huv
  rw [mixed_candidate_weighted_codegree,Finset.sum_div]
  exact Finset.sum_le_sum (fun i _=>h i u v huv)
end Oberwolfach
