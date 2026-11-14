module

public import Oberwolfach.PhysicalRimResourceResidual
public import Oberwolfach.LongPreparationBadGraphBounds

@[expose] public section
/-! A realised deletion contributes its degree directly to the physical
residual; it is not multiplied by a sampling density. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U W W₀:Type} [Fintype V] [Fintype U] [Fintype W] [Fintype W₀]
  [DecidableEq V] [DecidableEq U] [DecidableEq W] [DecidableEq W₀]

theorem physical_rim_residual_after_deletion
    (φ:W↪Sym2 V⊕(V×U)) (f:W₀↪W) (D:SimpleGraph V)
    (covered:Finset W₀)
    (hdeleted:∀ w:W, (∀z:W₀,f z≠w) → ∀x y,
      φ w=Sum.inl s(x,y) → x≠y → D.Adj x y):
    physicalRimResidualGraph φ (covered.map f) ≤
      physicalRimResidualGraph (f.trans φ) covered ⊔ D :=by
  intro x y h
  obtain ⟨hxy,w,hw,hφ⟩:=h
  by_cases hex:∃z:W₀,f z=w
  · obtain ⟨z,rfl⟩:=hex
    have hz:z∉covered:=by
      intro hz
      apply hw
      exact Finset.mem_map.mpr ⟨z,hz,rfl⟩
    exact (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inl ⟨hxy,z,hz,hφ⟩)
  · exact (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inr
      (hdeleted w (fun z hz=>hex ⟨z,hz⟩) x y hφ hxy))

theorem physical_rim_residual_degree_after_deletion
    (φ:W↪Sym2 V⊕(V×U)) (f:W₀↪W) (D:SimpleGraph V)
    (covered:Finset W₀)
    (hdeleted:∀ w:W, (∀z:W₀,f z≠w) → ∀x y,
      φ w=Sum.inl s(x,y) → x≠y → D.Adj x y)
    (a γ δ:ℝ) (hγ:0≤γ) (hD:∀x,(D.degree x:ℝ)≤δ)
    (hlarge:∀x,a*(Fintype.card V:ℝ)≤(rimIncidentResources (f.trans φ) x).card →
      (((rimIncidentResources (f.trans φ) x\covered).card:ℕ):ℝ)≤γ*(rimIncidentResources (f.trans φ) x).card):
    ∀x,((physicalRimResidualGraph φ (covered.map f)).degree x:ℝ)≤
      max a γ*(Fintype.card V:ℝ)+δ :=by
  intro x
  have hm:((physicalRimResidualGraph φ (covered.map f)).degree x:ℝ)≤
      ((physicalRimResidualGraph (f.trans φ) covered ⊔ D).degree x:ℝ):=by
    exact_mod_cast SimpleGraph.degree_le_of_le
      (physical_rim_residual_after_deletion φ f D covered hdeleted)
  have hu:(((physicalRimResidualGraph (f.trans φ) covered ⊔ D).degree x):ℝ)≤
      ((physicalRimResidualGraph (f.trans φ) covered).degree x:ℝ)+D.degree x:=by
    exact_mod_cast graph_degree_sup_le (physicalRimResidualGraph (f.trans φ) covered) D x
  have hr:=physical_rim_residual_degree_from_large_coverage (f.trans φ) covered a γ hγ hlarge x
  linarith [hD x]
end Oberwolfach
