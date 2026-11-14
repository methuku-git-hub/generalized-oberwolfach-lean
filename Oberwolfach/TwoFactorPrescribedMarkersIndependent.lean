module

public import Oberwolfach.TwoFactorExtendedMarkers

@[expose] public section
/-! The residual prescribed set formed from final-path endpoints and
surviving selected-path markers is independent. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem two_factor_residual_prescribed_markers_independent
    (F Q:SimpleGraph V) (hF:F.IsRegularOfDegree 2) (hQ:Q≤F)
    (s₁ s₂:Finset I) (u v:I→V) (P:∀ i,F.Walk (u i) (v i))
    (hp:∀i∈s₁∪s₂,(P i).IsPath)
    (hP:(↑(s₁∪s₂):Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset))
    (c d:ℕ) (hc:3≤c) (hlen:∀i∈s₁∪s₂,(P i).length=c*d+4)
    (R:Finset V):
    let A₀ := (s₁.biUnion (fun i=>{(P i).getVert 2,(P i).getVert (2+c*d)})) ∪
      (R ∩ s₂.biUnion (fun i=>(Finset.range (d+1)).image (fun j=>(P i).getVert (2+c*j))));
    ∀ x∈A₀,∀ y∈A₀,¬Q.Adj x y := by
  let s:=s₁∪s₂
  let T:=fun _ : I=>(Finset.range (d+1)).image (fun j=>2+c*j)
  let A:=s.biUnion (fun i=>(T i).image (P i).getVert)
  have hind:=two_factor_extended_markers_independent F hF s u v P hp hP c d hc hlen
  have hsub:(s₁.biUnion (fun i=>{(P i).getVert 2,(P i).getVert (2+c*d)})) ∪
      (R ∩ s₂.biUnion (fun i=>(Finset.range (d+1)).image (fun j=>(P i).getVert (2+c*j))))⊆A := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx|hx
    · obtain ⟨i,hi,hx⟩:=Finset.mem_biUnion.mp hx
      have hi':i∈s := Finset.mem_union_left _ hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl
      · apply Finset.mem_biUnion.mpr
        refine ⟨i,hi',Finset.mem_image.mpr ⟨2,?_,rfl⟩⟩
        exact Finset.mem_image.mpr ⟨0,by simp,by simp⟩
      · apply Finset.mem_biUnion.mpr
        refine ⟨i,hi',Finset.mem_image.mpr ⟨2+c*d,?_,rfl⟩⟩
        exact Finset.mem_image.mpr ⟨d,by simp,rfl⟩
    · obtain ⟨i,hi,hx⟩:=Finset.mem_biUnion.mp (Finset.mem_inter.mp hx).2
      obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hx
      apply Finset.mem_biUnion.mpr
      refine ⟨i,Finset.mem_union_right _ hi,Finset.mem_image.mpr ⟨2+c*j,?_,rfl⟩⟩
      exact Finset.mem_image.mpr ⟨j,hj,rfl⟩
  dsimp only
  intro x hx y hy hxy
  exact hind x (hsub hx) y (hsub hy) (hQ hxy)
end Oberwolfach
