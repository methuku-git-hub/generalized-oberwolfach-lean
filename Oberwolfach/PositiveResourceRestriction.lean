module

public import Oberwolfach.FractionalResourceMatching

@[expose] public section
/-! Removing zero-weight candidates leaves all weighted degree, codegree,
and coefficient-test masses unchanged. Candidate identifiers are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E A:Type} [Fintype V] [Fintype E] [Fintype A] [DecidableEq V]

abbrev PositiveResource (w:E→ℝ):= {e:E // 0<w e}

theorem positive_resource_weighted_sum
    (w:E→ℝ) (hw:∀e,0≤w e) (g:E→ℝ):
    (∑e:PositiveResource w,g e.val*w e.val)=∑e,g e*w e := by
  have he:=Finset.sum_subtype (F:=inferInstance) (p:=fun e:E=>0<w e)
    (Finset.univ.filter (fun e:E=>0<w e)) (by intro x;simp) (fun e=>g e*w e)
  rw [←he,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h:0<w e
  · simp [h]
  · have hz:w e=0:=le_antisymm (le_of_not_gt h) (hw e)
    simp [h,hz]

theorem positive_resource_degree
    (R:E→Finset V) (w:E→ℝ) (hw:∀e,0≤w e) (v:V):
    hypergraphWeightedDegree (fun e:PositiveResource w=>R e.val) (fun e=>w e.val) v=
      hypergraphWeightedDegree R w v := by
  unfold hypergraphWeightedDegree
  have hh:=positive_resource_weighted_sum w hw (fun e=>if v∈R e then (1:ℝ) else 0)
  simpa only [ite_mul,one_mul,zero_mul] using hh

theorem positive_resource_codegree
    (R:E→Finset V) (w:E→ℝ) (hw:∀e,0≤w e) (u v:V):
    (∑e:PositiveResource w,if u∈R e.val ∧ v∈R e.val then w e.val else 0)=
      ∑e,if u∈R e ∧ v∈R e then w e else 0 := by
  have hh:=positive_resource_weighted_sum w hw (fun e=>if u∈R e ∧ v∈R e then (1:ℝ) else 0)
  simpa only [ite_mul,one_mul,zero_mul] using hh
end Oberwolfach
