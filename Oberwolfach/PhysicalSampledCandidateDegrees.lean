module

public import Oberwolfach.PhysicalSampledCandidateRestriction

@[expose] public section
/-! Weighted degrees and codegrees of the realized candidates on their
physical resources, with all candidate identities retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B C:Type} [Fintype A] [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem physical_sampled_candidate_degree (φ:A→B) (R:C→Finset A) (w:C→ℝ) (σ:A→Bool)
    (hinj:∀c,Set.InjOn φ (↑(R c):Set A)) (x:PhysicalSampledActive φ σ):
    hypergraphWeightedDegree (physicalSampledCandidateSet φ R σ) (fun c=>w c.val) x=
      ∑a∈Finset.univ.filter (fun a=>φ a=x.val),
        if σ a=true then resourcePatternLoad R w (fun _ _=>true) a σ else 0 :=by
  have hh:=physical_sampled_degree_eq_active_root_loads φ R w σ hinj x.val
  apply Eq.trans _ hh
  unfold hypergraphWeightedDegree
  simp only [physical_sampled_candidate_set_mem]
  have he:=Finset.sum_subtype (F:=inferInstance) (p:=fun c:C=>∀a∈R c,σ a=true)
    (Finset.univ.filter (fun c:C=>∀a∈R c,σ a=true)) (by intro c;simp)
    (fun c=>if x.val∈(R c).image φ then w c else 0)
  rw [←he,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hs:∀a∈R c,σ a=true <;> by_cases hx:x.val∈(R c).image φ <;> simp [hs,hx]

theorem physical_sampled_candidate_codegree_le (φ:A→B) (R:C→Finset A) (w:C→ℝ) (σ:A→Bool)
    (hw:∀c,0≤w c) (x y:PhysicalSampledActive φ σ):
    (∑c:PhysicalSampledCandidate R σ,
      if x∈physicalSampledCandidateSet φ R σ c ∧ y∈physicalSampledCandidateSet φ R σ c then w c.val else 0)≤
    (∑c:C,if x.val∈(R c).image φ ∧ y.val∈(R c).image φ then w c else 0) :=by
  simp only [physical_sampled_candidate_set_mem]
  have he:=Finset.sum_subtype (F:=inferInstance) (p:=fun c:C=>∀a∈R c,σ a=true)
    (Finset.univ.filter (fun c:C=>∀a∈R c,σ a=true)) (by intro c;simp)
    (fun c=>if x.val∈(R c).image φ ∧ y.val∈(R c).image φ then w c else 0)
  rw [←he]
  exact Finset.sum_le_univ_sum_of_nonneg (fun c=>by split_ifs <;> simp_all)
end Oberwolfach
