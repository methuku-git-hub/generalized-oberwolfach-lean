module

public import Oberwolfach.FixedAbsorberSelectedSupport
public import Oberwolfach.MarkedResourceRimGraph

@[expose] public section
/-! Every physical rim edge of the fixed absorber is an edge of the selected
sample, even when its endpoints lie outside the first protected pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]

theorem long_fixed_absorber_rim_is_selected
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (g₀:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g₀) t)
    (j₁:Color) (C:Finset (Finset V⊕(V×U))) (X:Finset V) (Z:Finset U):
    let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedMarkedCollapse e (σ e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g₀ t J g₀ j₁
    MarkedFixedTerminalAbsorber P π d m raw H C X Z→
      markedResourceRimGraph C≤longSelectedPhysicalGraph P π d σ:=by
  intro raw H habs x y hC
  have hres:Sum.inl ({x,y}:Finset V)∈C:=(Finset.mem_filter.mp hC.2).2
  have hsub:=fixed_absorber_selected_layer_subset P π d m σ g₀ t J j₁ C X Z habs
  obtain ⟨z,hz,heq⟩:=Finset.mem_image.mp (hsub hres)
  have heq':physicalResourceToFinite z=physicalResourceToFinite (Sum.inl s(x,y):Sym2 V⊕(V×U)):=by
    simpa only [physicalResourceToFinite,Sum.map_inl,Sym2.toFinset_mk_eq] using heq
  have hz':z=Sum.inl s(x,y):=physical_resource_to_finite_injective heq'
  subst z
  have he:s(x,y)∈(longSelectedPhysicalGraph P π d σ).edgeFinset:=by
    simpa only [wheelLayerPhysicalResources,Finset.mem_union,Finset.mem_image,Sum.inl.injEq,
      Sum.inr_ne_inl,and_false,exists_false,or_false,exists_eq_right] using hz
  exact SimpleGraph.mem_edgeFinset.mp he
end Oberwolfach
