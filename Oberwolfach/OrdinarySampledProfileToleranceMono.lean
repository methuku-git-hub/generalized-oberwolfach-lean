module

public import Oberwolfach.OrdinarySampledProfileProperty
public import Oberwolfach.OrdinarySampledTriangleProfileProperty

@[expose] public section
/-! The fixed weights and sampled host are unchanged when a weighted-degree
error tolerance is enlarged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]
theorem ordinary_sampled_profile_tolerance_mono (r:ℕ)
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawWheelOutcome V U Γ Color)
    (pmin smin:ℝ) (j:Color) (β η θ a b:ℝ) (hη:η≤θ)
    (h:ordinarySampledProfileProperty (r:=r) P F π d σ pmin smin j β η a b):
    ordinarySampledProfileProperty (r:=r) P F π d σ pmin smin j β θ a b := by
  obtain ⟨hgeo,w,hw,hdeg⟩:=h
  exact ⟨hgeo,w,hw,fun u u' hne v hv=>(hdeg u u' hne v hv).trans hη⟩

theorem ordinary_sampled_triangle_tolerance_mono
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawWheelOutcome V U Γ Color)
    (pmin smin:ℝ) (j:Color) (β η θ a b:ℝ) (hη:η≤θ)
    (h:ordinarySampledTriangleProfileProperty P F π d σ pmin smin j β η a b):
    ordinarySampledTriangleProfileProperty P F π d σ pmin smin j β θ a b := by
  obtain ⟨hgeo,w,hw,hdeg⟩:=h
  exact ⟨hgeo,w,hw,fun u u' hne v hv=>(hdeg u u' hne v hv).trans hη⟩
end Oberwolfach
