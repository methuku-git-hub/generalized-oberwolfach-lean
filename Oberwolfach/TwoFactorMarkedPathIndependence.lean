module

public import Oberwolfach.TwoFactorPathNeighborSupport

@[expose] public section
/-! Marked internal vertices separated along vertex-disjoint extended paths
are independent in the original two-factor. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem two_factor_spaced_path_vertices_independent
    (F:SimpleGraph V) (hF:F.IsRegularOfDegree 2)
    (s:Finset I) (u v:I→V) (P:∀ i,F.Walk (u i) (v i))
    (hp:∀i∈s,(P i).IsPath)
    (hP:(↑s:Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset))
    (T:I→Finset ℕ)
    (hint:∀i∈s,∀a∈T i,0<a ∧ a<(P i).length)
    (hspace:∀i∈s,∀a∈T i,∀b∈T i,a≠b→a+1≠b ∧ b+1≠a):
    ∀ x∈s.biUnion (fun i=>(T i).image (P i).getVert),
      ∀ y∈s.biUnion (fun i=>(T i).image (P i).getVert),¬F.Adj x y := by
  intro x hx y hy hxy
  obtain ⟨i,hi,hx⟩:=Finset.mem_biUnion.mp hx
  obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hx
  obtain ⟨j,hj,hy⟩:=Finset.mem_biUnion.mp hy
  obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp hy
  have hai:=hint i hi a ha
  have hbj:=hint j hj b hb
  by_cases hij:i=j
  · subst j
    have hab:a≠b := by
      intro h;subst b
      exact F.irrefl hxy
    have hc:=two_factor_path_adjacent_indices F hF (P i) (hp i hi) a b
      (by omega) hai.2 (Nat.le_of_lt hbj.2) hxy
    have hs:=hspace i hi a ha b hb hab
    rcases hc with hc|hc
    · exact hs.2 hc
    · exact hs.1 hc
  · have hys : (P j).getVert b∈(P i).support.toFinset :=
      two_factor_internal_neighbors_on_path F hF (P i) (hp i hi) a (by omega) hai.2 _ hxy
    have hyj : (P j).getVert b∈(P j).support.toFinset := by
      apply List.mem_toFinset.mpr
      exact (P j).getVert_mem_support b
    exact Finset.disjoint_left.mp (hP hi hj hij) hys hyj
end Oberwolfach
