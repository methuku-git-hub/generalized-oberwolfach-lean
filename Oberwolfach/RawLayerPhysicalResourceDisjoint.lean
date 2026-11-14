module

public import Oberwolfach.PhysicalSamplingLayerDisjoint
public import Oberwolfach.RawApproximateRetainedSelectedSpokes

@[expose] public section
/-! Physical resources in the raw approximate layer and retained selected
layer are disjoint, even after the selected interval colour is trimmed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def wheelLayerPhysicalResources (G:SimpleGraph V) (H:Bool→V→U→Prop):Finset (Sym2 V⊕(V×U)):=
  G.edgeFinset.image Sum.inl ∪ (Finset.univ.filter (fun vu:V×U=>∃b,H b vu.1 vu.2)).image Sum.inr

theorem raw_approximate_and_retained_selected_physical_disjoint
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (g₀ g₂:Γ) (hg:g₂≠g₀) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g₀) t)
    (j₁ j₂:Color) (hj:j₂≠j₁):
    Disjoint
      (wheelLayerPhysicalResources (longApproximatePhysicalGraph P π d σ)
        (rawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g₂ j₂))
      (wheelLayerPhysicalResources (longSelectedPhysicalGraph P π d σ)
        (retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g₀ t J g₀ j₁)) :=by
  apply Finset.disjoint_left.mpr
  intro z hzA hzS
  simp only [wheelLayerPhysicalResources,Finset.mem_union,Finset.mem_image] at hzA hzS
  rcases hzA with ⟨a,ha,rfl⟩|⟨a,ha,rfl⟩
  · rcases hzS with ⟨e,he,heq⟩|⟨e,he,heq⟩
    · have hae:a=e:=(Sum.inl.inj heq).symm
      subst e
      induction a using Sym2.ind with
      | _ x y=>
        have hA: (longApproximatePhysicalGraph P π d σ).Adj x y:=SimpleGraph.mem_edgeFinset.mp ha
        have hS: (longSelectedPhysicalGraph P π d σ).Adj x y:=SimpleGraph.mem_edgeFinset.mp he
        have hd:=selected_and_approximate_rim_graphs_disjoint P π d σ
        exact (disjoint_iff_inf_le.mp hd) ⟨hS,hA⟩
    · cases heq
  · rcases hzS with ⟨e,he,heq⟩|⟨e,he,heq⟩
    · cases heq
    · have hae:a=e:=(Sum.inr.inj heq).symm
      subst e
      obtain ⟨b,hb⟩:=(Finset.mem_filter.mp ha).2
      obtain ⟨b',hb'⟩:=(Finset.mem_filter.mp he).2
      exact raw_approximate_spoke_avoids_retained_selected π d (fun e=>σ (Sum.inr e)) g₀ g₂ hg t J j₁ j₂ hj a.1 a.2 b b' ⟨hb,hb'⟩
/-- Consequently every approximate resource family avoids any preselected
absorber contained in the retained selected layer. -/
theorem raw_approximate_resources_avoid_selected_absorber
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (g₀ g₂:Γ) (hg:g₂≠g₀) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g₀) t)
    (j₁ j₂:Color) (hj:j₂≠j₁) (Approx Absorber:Finset (Sym2 V⊕(V×U)))
    (hApprox:Approx⊆wheelLayerPhysicalResources (longApproximatePhysicalGraph P π d σ)
      (rawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g₂ j₂))
    (hAbsorber:Absorber⊆wheelLayerPhysicalResources (longSelectedPhysicalGraph P π d σ)
      (retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g₀ t J g₀ j₁)):
    Disjoint Approx Absorber :=by
  exact (raw_approximate_and_retained_selected_physical_disjoint P π d σ g₀ g₂ hg t J j₁ j₂ hj).mono hApprox hAbsorber
end Oberwolfach
