module

public import Oberwolfach.RetainedAndRawIntervalGeometry
public import Oberwolfach.BufferedMarkerAnchorEmbedding

@[expose] public section
/-! The same mixed outcome provides the actual final-plus-approximate
interval labels for a disjoint family of buffered source paths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem mixed_outcome_buffered_anchor_embedding
    {X V U Γ Color:Type} [DecidableEq X] [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U] [DecidableEq Γ]
    (π:Equiv.Perm V) (d c:ℕ) (hd:1≤d) (hc:0<c)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (g₀ g₁:Γ) (hclasses:g₀≠g₁) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (w:U):
    let I:=retainedAndRawIntervalIndex π d σ g₀ g₁ t J w
    let root:=retainedAndRawIntervalRoot π d σ g₀ g₁ t J w
    ∀(ext:∀i:I,Fin (c*d+5)↪X),
    (∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))→
    let A:=Finset.univ.image (fun z:I×Fin (d+1)=>bufferedMarker c d (ext z.1) z.2)
    ∃f:{x // x∈A}↪V,
      ∀i (j:Fin (d+1)),f ⟨bufferedMarker c d (ext i) j,Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩⟩=(π^j.val) (root i):=by
  classical
  intro I root ext hsrc A
  have hgeom:=retained_and_raw_interval_geometry π d hd hnoshort σ g₀ g₁ hclasses t J w
  exact buffered_marker_anchor_embedding c d hc ext hsrc π root hgeom.1 hgeom.2
end Oberwolfach
