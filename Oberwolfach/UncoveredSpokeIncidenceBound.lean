module

public import Oberwolfach.RawPackedMissingSpokes

@[expose] public section
/-! Transfer an uncovered physical-spoke count to the matching's uncovered
incidence count through an injective resource representation. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem uncovered_spoke_incidence_bound
    {V R:Type} [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R]
    (Available Covered:Finset V) (Inc Matched:Finset R) (f:V→R)
    (hinj:Function.Injective f) (hinc:∀v∈Available,f v∈Inc)
    (hcovered:∀v∈Available,f v∈Matched→v∈Covered):
    (Available\Covered).card≤(Inc\Matched).card:=by
  have hsub:(Available\Covered).image f⊆Inc\Matched:=by
    intro z hz
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
    have hh:=Finset.mem_sdiff.mp hv
    apply Finset.mem_sdiff.mpr
    refine ⟨hinc v hh.1,?_⟩
    intro h
    exact hh.2 (hcovered v hh.1 h)
  have hh:=Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at hh
  exact hh
end Oberwolfach
