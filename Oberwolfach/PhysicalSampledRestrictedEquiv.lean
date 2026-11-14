module

public import Oberwolfach.PhysicalSampledCandidateRestriction
public import Oberwolfach.BernoulliVertexSampling

@[expose] public section
/-! Realized typed candidates are precisely the restrictions to active
typed resources; this preserves each candidate identifier and weight. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A C:Type} [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq C]

def physicalSampledRestrictedEquiv (R:C→Finset A) (σ:A→Bool):
    PhysicalSampledCandidate R σ ≃
      RestrictedResource R (Function.Embedding.subtype (fun a=>a∈bernoulliVertexSet σ)) where
  toFun c:=⟨c.val,by
    intro a ha
    exact ⟨⟨a,(mem_bernoulliVertexSet σ a).mpr (c.property a ha)⟩,rfl⟩⟩
  invFun c:=⟨c.val,by
    intro a ha
    obtain ⟨x,hx⟩:=c.property a ha
    have hh:σ x.val=true:=(mem_bernoulliVertexSet σ x.val).mp x.property
    simpa only [Function.Embedding.coe_subtype] using hx ▸ hh⟩
  left_inv c:=Subtype.ext rfl
  right_inv c:=Subtype.ext rfl

theorem physical_sampled_restricted_sum (R:C→Finset A) (σ:A→Bool) (f:C→ℝ):
    (∑c:PhysicalSampledCandidate R σ,f c.val)=
      ∑c:RestrictedResource R (Function.Embedding.subtype (fun a=>a∈bernoulliVertexSet σ)),f c.val :=by
  calc
    _ = ∑c:PhysicalSampledCandidate R σ,f ((physicalSampledRestrictedEquiv R σ) c).val := by
      apply Finset.sum_congr rfl
      intro c _
      rfl
    _ = _ := Equiv.sum_comp (physicalSampledRestrictedEquiv R σ) (fun c=>f c.val)
end Oberwolfach
