module

public import Oberwolfach.PhysicalSampledCandidateRestriction

@[expose] public section
/-! A matching row on active physical resources has exactly the same
uncovered cardinality when viewed in the underlying physical universe. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B C:Type} [Fintype A] [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B] [DecidableEq C]

def physicalSampledRow (φ:A→B) (σ:A→Bool) (T:Finset B):Finset (PhysicalSampledActive φ σ):=
  Finset.univ.filter (fun x=>x.val∈T)

theorem physical_sampled_uncovered_row_card
    (φ:A→B) (R:C→Finset A) (σ:A→Bool) (T:Finset B)
    (L:Finset (PhysicalSampledCandidate R σ)):
    let Q:=physicalSampledCandidateSet φ R σ
    let row:=physicalSampledRow φ σ T
    let covered:Finset B:=(L.biUnion Q).image Subtype.val;
    (row\L.biUnion Q).card=
      ((T.filter (fun x=>∃a,σ a=true ∧ φ a=x))\covered).card :=by
  intro Q row covered
  have he:(row\L.biUnion Q).image Subtype.val=
      (T.filter (fun x=>∃a,σ a=true ∧ φ a=x))\covered:=by
    ext x
    constructor
    · intro hx
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hx
      have hv':=Finset.mem_sdiff.mp hv
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv'.1).2,v.property⟩,?_⟩
      intro hcov
      obtain ⟨w,hw,hval⟩:=Finset.mem_image.mp hcov
      have heq:w=v:=Subtype.ext hval
      exact hv'.2 (heq ▸ hw)
    · intro hx
      have hx':=Finset.mem_sdiff.mp hx
      have hT: x∈T:=(Finset.mem_filter.mp hx'.1).1
      have ha:∃a,σ a=true ∧ φ a=x:=(Finset.mem_filter.mp hx'.1).2
      let v:PhysicalSampledActive φ σ:=⟨x,ha⟩
      refine Finset.mem_image.mpr ⟨v,Finset.mem_sdiff.mpr ⟨?_,?_⟩,rfl⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hT⟩
      · intro hv
        exact hx'.2 (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
  have hc:=congrArg Finset.card he
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hc
  exact hc
end Oberwolfach
