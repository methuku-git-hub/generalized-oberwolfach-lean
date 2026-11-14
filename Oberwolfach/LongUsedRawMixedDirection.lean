module

public import Oberwolfach.LongRawResourceMixedDirection
public import Oberwolfach.PhysicalRimResourceResidual

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color C:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color] [Fintype C] [DecidableEq C]

theorem long_used_raw_mixed_direction
    (G:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (raw:RawMarkedOutcome V U Γ Color) (g:Γ) (j:Color):
    let T:=bernoulliVertexSet (typedMarkedResourceState (rawMarkedPairRims G π d raw) (rawMarkedPairSpokes π d raw g j))
    let φ:=markedRawSampledPhysicalEmbedding G π d raw g j
    ∀(R:C→Finset {z // z∈T}) (M:Finset C) x y,
      (physicalRimCandidateUnion φ R M).Adj x y→
      rawMixedPhysicalArc G π d raw x y ∨ rawMixedPhysicalArc G π d raw y x:=by
  intro T φ R M x y h
  obtain ⟨_,c,hc,w,hw,hφ⟩:=h
  exact long_raw_sampled_rim_has_mixed_direction G π d raw g j x y w hφ
end Oberwolfach
