module

public import Oberwolfach.EndpointDeepCountInputs
public import Oberwolfach.OrdinaryPhysicalSubsetDomains

@[expose] public section
/-! Transport the deeper two-domain estimates to every physical root set
contained in the rim side and every hub set contained in the hub side. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem endpoint_deep_counts_physical (P Q F:SimpleGraph V) (H:V→U→Prop)
    (A:Finset V) (B:Finset U) (pR pH ε:ℝ) (data:EndpointTypedDeepCounts P Q F H A B pR pH ε):
    EndpointPhysicalDeepCounts P Q F H A B pR pH ε:=by
  constructor
  · intro S J hSleft hJB hSc hJc hSJ
    obtain ⟨S₀,hS,hScard⟩:=ordinary_physical_left_subset_image S hSleft
    have hJright:J⊆Finset.univ.image (Sum.inr:U→V⊕U):=by
      intro z hz
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp (hJB hz)
      exact Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩
    obtain ⟨J₀,hJ,hJcard⟩:=ordinary_physical_right_subset_image J hJright
    have hJ₀:J₀⊆B:=by
      intro u hu
      have hu':Sum.inr u∈J:=by rw [←hJ];exact Finset.mem_image.mpr ⟨u,hu,rfl⟩
      have hb:=hJB hu'
      simpa using hb
    have hh:=data.rows S₀ J₀ hJ₀ (by omega) (by omega) (by omega)
    rw [←hS,←hJ]
    have hpdiff:
        common (A.image (Sum.inl:V→V⊕U)) (S₀.image Sum.inl)
          (fun v=>((ordinaryPhysicalGraph P (fun _ _=>False))\
            (ordinaryPhysicalGraph F (fun _ _=>False))).neighborFinset v)=
        (common A S₀ (fun v=>(P\F).neighborFinset v)).image Sum.inl:=by
      ext z
      cases z <;> simp [common,ordinaryPhysicalGraph,SimpleGraph.sdiff_adj,SimpleGraph.mem_neighborFinset]
    rw [hpdiff,ordinary_physical_common_rim,ordinary_physical_common_spoke_rows]
    simpa only [Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ Sum.inr_injective] using hh
  · intro S hSleft hSc hfree
    obtain ⟨S₀,hS,hScard⟩:=ordinary_physical_left_subset_image S hSleft
    have hfree₀:∀v∈S₀,∀w∈S₀,¬F.Adj v w:=by
      intro v hv w hw hf
      have hv':Sum.inl v∈S:=by rw [←hS];exact Finset.mem_image.mpr ⟨v,hv,rfl⟩
      have hw':Sum.inl w∈S:=by rw [←hS];exact Finset.mem_image.mpr ⟨w,hw,rfl⟩
      exact hfree (Sum.inl v) hv' (Sum.inl w) hw' (by simpa [ordinaryPhysicalGraph] using hf)
    have hh:=data.indices S₀ (by omega) hfree₀
    rw [←hS,ordinary_physical_common_spoke_hubs]
    simpa only [Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ Sum.inr_injective] using hh
end Oberwolfach
