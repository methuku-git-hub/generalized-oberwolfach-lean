module

public import Oberwolfach.ResidualDeletedPathLengthsSum
public import Oberwolfach.ResidualVertexCardGeneral
public import Oberwolfach.ResidualActualPathFamilyGraph

@[expose] public section
/-! Exact surviving vertex count for the actual paths, maximal selected
runs, and deleted cycle components. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V I J:Type} [Fintype V] [DecidableEq V] [DecidableEq I] [DecidableEq J]

theorem residual_actual_vertex_count (F:SimpleGraph V)
    (s₁ s₂:Finset I) (hs:Disjoint s₁ s₂) (u v:I→V) (P:∀i,F.Walk (u i) (v i))
    (hp:∀i∈s₁∪s₂,(P i).IsPath)
    (hP:(↑(s₁∪s₂):Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset))
    (c d:ℕ) (hc:0<c) (hd:0<d) (hlen:∀i∈s₁∪s₂,(P i).length=c*d+4)
    (T:I→Finset ℕ) (hT:∀i∈s₂,T i⊆Finset.range d)
    (t:Finset J) (root:J→V) (C:∀j,F.Walk (root j) (root j))
    (hcross:∀i∈s₁∪s₂,∀j∈t,Disjoint (P i).support.toFinset (C j).support.toFinset):
    let Z:=DeletedPathIndex s₁ s₂ d T
    let U:Z→V:=deletedPathStart F s₁ s₂ u v P c d T
    let W:Z→V:=deletedPathEnd F s₁ s₂ u v P c d T
    let paths:∀z:Z,F.Walk (U z) (W z):=deletedPathWalk F s₁ s₂ u v P c d T hT
    let Cset:=t.biUnion (fun j=>(C j).support.toFinset)
    let R:=Finset.univ \ (Cset ∪ Finset.univ.biUnion (fun z=>(paths z).support.toFinset \ {U z,W z}));
    R.card+Cset.card+c*d*s₁.card+c*(∑i∈s₂,(T i).card)=
      Fintype.card V+s₁.card+(∑i∈s₂,(selectedSegmentRuns d (T i)).card) := by
  let Z:=DeletedPathIndex s₁ s₂ d T
  let U:Z→V:=deletedPathStart F s₁ s₂ u v P c d T
  let W:Z→V:=deletedPathEnd F s₁ s₂ u v P c d T
  let paths:∀z:Z,F.Walk (U z) (W z):=deletedPathWalk F s₁ s₂ u v P c d T hT
  let Cset:=t.biUnion (fun j=>(C j).support.toFinset)
  have hprops:=deleted_path_family_properties F s₁ s₂ u v P hp c d hc hd hlen T hT
  have hdisj:(↑(Finset.univ:Finset Z):Set Z).PairwiseDisjoint (fun z=>(paths z).support.toFinset) := by
    intro z _ w _ hne
    exact deleted_path_family_vertex_disjoint F s₁ s₂ hs u v P hp hP c d hc hlen T hT z w hne
  have hC:∀z∈(Finset.univ:Finset Z),Disjoint Cset (paths z).support.toFinset := by
    intro z _
    apply Finset.disjoint_left.mpr
    intro x hx hz
    obtain ⟨j,hj,hxj⟩:=Finset.mem_biUnion.mp hx
    have hz':x∈(P (deletedPathParent z)).support.toFinset :=
      deleted_path_support_subset_parent F s₁ s₂ u v P c d hlen T hT z hz
    exact Finset.disjoint_left.mp (hcross (deletedPathParent z) (deleted_path_parent_mem z) j hj) hz' hxj
  have hcount:=residual_vertex_count_from_paths F (Finset.univ:Finset Z) U W paths
    (by intro z _;exact (hprops z).1) (by intro z _;exact (hprops z).2) hdisj Cset hC
  have hlength:=deleted_path_lengths_sum F s₁ s₂ u v P hp c d hc hlen T hT
  have hindex:=deleted_path_index_card s₁ s₂ d T
  dsimp only at hcount hlength ⊢
  rw [Finset.card_univ,hindex] at hcount
  dsimp only [Z,U,W,paths,Cset] at hcount ⊢
  rw [hlength] at hcount
  omega
end Oberwolfach
