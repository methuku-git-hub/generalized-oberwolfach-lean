module

public import Oberwolfach.PhysicalSampledRootLoads
public import Oberwolfach.ResourceRestriction

@[expose] public section
/-! Restrict to candidates whose own typed states are all present, while
matching on the common physical resource universe. Different typed states
may have the same physical image. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B C:Type} [Fintype A] [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B] [DecidableEq C]

abbrev PhysicalSampledActive (φ:A→B) (σ:A→Bool):Type :=
  {x:B // ∃a,σ a=true ∧ φ a=x}

abbrev PhysicalSampledCandidate (R:C→Finset A) (σ:A→Bool):Type :=
  {c:C // ∀a∈R c,σ a=true}

def physicalSampledCandidateSet (φ:A→B) (R:C→Finset A) (σ:A→Bool)
    (c:PhysicalSampledCandidate R σ):Finset (PhysicalSampledActive φ σ) :=
  Finset.univ.filter (fun x=>x.val∈(R c.val).image φ)

theorem physical_sampled_candidate_set_mem (φ:A→B) (R:C→Finset A) (σ:A→Bool)
    (c:PhysicalSampledCandidate R σ) (x:PhysicalSampledActive φ σ):
    x∈physicalSampledCandidateSet φ R σ c ↔ x.val∈(R c.val).image φ :=by
  simp [physicalSampledCandidateSet]

theorem physical_sampled_candidate_set_image (φ:A→B) (R:C→Finset A) (σ:A→Bool)
    (c:PhysicalSampledCandidate R σ):
    (physicalSampledCandidateSet φ R σ c).image Subtype.val=(R c.val).image φ :=by
  ext x
  constructor
  · rintro hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    exact (physical_sampled_candidate_set_mem φ R σ c y).mp hy
  · intro hx
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hx
    let y:PhysicalSampledActive φ σ:=⟨φ a,a,c.property a ha,rfl⟩
    exact Finset.mem_image.mpr ⟨y,(physical_sampled_candidate_set_mem φ R σ c y).mpr
      (Finset.mem_image.mpr ⟨a,ha,rfl⟩),rfl⟩

theorem physical_sampled_candidate_set_card (φ:A→B) (R:C→Finset A) (σ:A→Bool)
    (c:PhysicalSampledCandidate R σ) (hinj:Set.InjOn φ (↑(R c.val):Set A)):
    (physicalSampledCandidateSet φ R σ c).card=(R c.val).card :=by
  have he:=physical_sampled_candidate_set_image φ R σ c
  have h1:((physicalSampledCandidateSet φ R σ c).image Subtype.val).card=
      (physicalSampledCandidateSet φ R σ c).card:=Finset.card_image_of_injective _ Subtype.val_injective
  have h2:((R c.val).image φ).card=(R c.val).card:=Finset.card_image_iff.mpr hinj
  have hcard:=congrArg Finset.card he
  rw [h1,h2] at hcard
  exact hcard
end Oberwolfach
