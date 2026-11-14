module

public import Oberwolfach.PhysicalSampledMatchingRows

@[expose] public section
/-! A matching of realized candidates is a packing of the underlying
physical rim and spoke sets, retaining the original candidate identifiers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B C:Type} [Fintype A] [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem physical_sampled_matching_images_disjoint
    (φ:A→B) (R:C→Finset A) (σ:A→Bool)
    (L:Finset (PhysicalSampledCandidate R σ))
    (hL:∀c∈L,∀c'∈L,c≠c'→Disjoint (physicalSampledCandidateSet φ R σ c) (physicalSampledCandidateSet φ R σ c')):
    ∀c∈L,∀c'∈L,c≠c'→Disjoint ((R c.val).image φ) ((R c'.val).image φ) :=by
  intro c hc c' hc' hne
  have hh:=hL c hc c' hc' hne
  rw [←physical_sampled_candidate_set_image φ R σ c,←physical_sampled_candidate_set_image φ R σ c']
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨a,ha,hae⟩:=Finset.mem_image.mp hx
  obtain ⟨b,hb,hbe⟩:=Finset.mem_image.mp hy
  have hab:a=b:=Subtype.ext (hae.trans hbe.symm)
  exact Finset.disjoint_left.mp hh ha (hab ▸ hb)

theorem physical_sampled_matching_covered_image
    (φ:A→B) (R:C→Finset A) (σ:A→Bool)
    (L:Finset (PhysicalSampledCandidate R σ)):
    (L.biUnion (physicalSampledCandidateSet φ R σ)).image Subtype.val=
      L.biUnion (fun c=>(R c.val).image φ) :=by
  ext x
  simp only [Finset.mem_image,Finset.mem_biUnion]
  constructor
  · rintro ⟨a,⟨c,hc,ha⟩,rfl⟩
    exact ⟨c,hc,Finset.mem_image.mp ((physical_sampled_candidate_set_mem φ R σ c a).mp ha)⟩
  · rintro ⟨c,hc,a,ha,rfl⟩
    let v:PhysicalSampledActive φ σ:=⟨φ a,a,c.property a ha,rfl⟩
    refine ⟨v,⟨c,hc,?_⟩,rfl⟩
    exact (physical_sampled_candidate_set_mem φ R σ c v).mpr (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
end Oberwolfach
