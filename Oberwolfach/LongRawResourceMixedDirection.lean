module

public import Oberwolfach.MarkedRawSampledPhysicalEmbedding
public import Oberwolfach.RawMixedPhysicalArcHost

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]

theorem long_raw_sampled_rim_has_mixed_direction
    (G:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (raw:RawMarkedOutcome V U Γ Color) (g:Γ) (j:Color)
    (x y:V)
    (w:{z // z∈bernoulliVertexSet (typedMarkedResourceState (rawMarkedPairRims G π d raw) (rawMarkedPairSpokes π d raw g j))})
    (h:markedRawSampledPhysicalEmbedding G π d raw g j w=Sum.inl s(x,y)):
    rawMixedPhysicalArc G π d raw x y ∨ rawMixedPhysicalArc G π d raw y x:=by
  obtain ⟨z,hz⟩:=w
  have hs:typedMarkedResourceState (rawMarkedPairRims G π d raw) (rawMarkedPairSpokes π d raw g j) z=true:=
    (mem_bernoulliVertexSet _ _).mp hz
  cases z with
  | inr a=>
    obtain ⟨b,v,u⟩:=a
    simp [markedRawSampledPhysicalEmbedding,markedResourceTypeEquiv_spoke,typedResourcePhysical] at h
  | inl a=>
    cases a with
    | inl a=>
      obtain ⟨v,u⟩:=a
      have hr:markedPhysicalRim G π (3*d) (fun e=>raw (Sum.inl e)) false v u=1:=by
        simpa [typedMarkedResourceState,rawMarkedPairRims] using hs
      have he:s(v,u)=s(x,y):=by
        simpa [markedRawSampledPhysicalEmbedding,markedResourceTypeEquiv_ordinary,typedResourcePhysical] using h
      rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact Or.inl (Or.inl (by simpa [rawMarkedPairRims] using hr))
      · exact Or.inr (Or.inl (by simpa [rawMarkedPairRims] using hr))
    | inr a=>
      obtain ⟨v,u⟩:=a
      have hr:markedPhysicalRim G π (3*d) (fun e=>raw (Sum.inl e)) true v u=1:=by
        simpa [typedMarkedResourceState,rawMarkedPairRims] using hs
      have he:s(v,π u)=s(x,y):=by
        simpa [markedRawSampledPhysicalEmbedding,markedResourceTypeEquiv_marked,typedResourcePhysical] using h
      rcases Sym2.eq_iff.mp he with ⟨hv,hu⟩|⟨hv,hu⟩
      · subst x;subst y
        exact Or.inl (Or.inr (by simpa [rawMarkedPairRims] using hr))
      · subst x;subst y
        exact Or.inr (Or.inr (by simpa [rawMarkedPairRims] using hr))
end Oberwolfach
