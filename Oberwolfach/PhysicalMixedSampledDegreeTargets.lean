module

public import Oberwolfach.PhysicalSampledCandidateDegrees
public import Oberwolfach.MixedApproximateResourceAggregation
public import Oberwolfach.FiniteFiberCombinedUnitLoad

@[expose] public section
/-! Family-wise root loads on one typed sample give near-unit physical
degrees once the active-fiber targets add to one. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I A V:Type} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
  [Fintype V] [DecidableEq V] {E:I→Type} [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]

theorem physical_mixed_sampled_degree_from_targets
    (φ:A→V) (R:∀i,E i→Finset A) (w:∀i,E i→ℝ) (σ:A→Bool)
    (hinj:∀i c,Set.InjOn φ (↑(R i c):Set A))
    (M:ℕ) (hM:∀x,(Finset.univ.filter (fun a=>φ a=x)).card≤M)
    (target:I→A→ℝ) (τ t:ℝ) (ht:0≤t)
    (htarget:∀x:PhysicalSampledActive φ σ,
      ∑a∈Finset.univ.filter (fun a=>φ a=x.val ∧ σ a=true),∑i,target i a=1)
    (hload:∀i a,σ a=true→
      |resourcePatternLoad (R i) (w i) (fun _ _=>true) a σ-target i a|≤t+τ*target i a)
    (x:PhysicalSampledActive φ σ):
    |hypergraphWeightedDegree (physicalSampledCandidateSet φ (mixedCandidateResources R) σ)
        (fun c=>mixedCandidateWeight w c.val) x-1|≤(M:ℝ)*(Fintype.card I:ℝ)*t+τ :=by
  let T:=Finset.univ.filter (fun a=>φ a=x.val ∧ σ a=true)
  have hcard:T.card≤M:=by
    apply (Finset.card_le_card ?_).trans (hM x.val)
    intro a ha
    simp only [T,Finset.mem_filter,Finset.mem_univ,true_and] at ha ⊢
    exact ha.1
  have hmix (a:A):resourcePatternLoad (mixedCandidateResources R) (mixedCandidateWeight w) (fun _ _=>true) a σ=
      ∑i,resourcePatternLoad (R i) (w i) (fun _ _=>true) a σ:=by
    unfold resourcePatternLoad mixedCandidateResources mixedCandidateWeight
    rw [Fintype.sum_sigma]
  have hrestrict (f:A→ℝ):
      (∑a∈Finset.univ.filter (fun a=>φ a=x.val),if σ a=true then f a else 0)=∑a∈T,f a:=by
    dsimp [T]
    rw [Finset.sum_filter,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases he:φ a=x.val <;> by_cases hs:σ a=true <;> simp [he,hs]
  rw [physical_sampled_candidate_degree φ (mixedCandidateResources R) (mixedCandidateWeight w) σ
    (fun c=>hinj c.1 c.2) x]
  simp_rw [hmix]
  rw [hrestrict]
  have hh:=finite_fiber_combined_unit_load T (fun a i=>target i a)
    (fun a i=>resourcePatternLoad (R i) (w i) (fun _ _=>true) a σ) τ t (htarget x) (by
      intro a ha i
      have hs:σ a=true:=(Finset.mem_filter.mp ha).2.2
      exact hload i a hs)
  have hc:(T.card:ℝ)≤M:=by exact_mod_cast hcard
  have hi:0≤(Fintype.card I:ℝ):=by positivity
  have hprod:0≤(Fintype.card I:ℝ)*t:=mul_nonneg hi ht
  have hscale:=mul_le_mul_of_nonneg_right hc hprod
  nlinarith
end Oberwolfach
