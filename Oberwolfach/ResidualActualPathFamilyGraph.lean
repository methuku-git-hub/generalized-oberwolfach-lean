module

public import Oberwolfach.ResidualDeletedIndexFinite
public import Oberwolfach.ResidualDeletionGraph

@[expose] public section
/-! Apply the residual graph count to the actual final paths and maximal
selected-run subpaths of the extended path family. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V I J:Type} [Fintype V] [DecidableEq V] [DecidableEq I] [DecidableEq J]

theorem residual_graph_for_actual_path_family (F:SimpleGraph V) (hF:F.IsRegularOfDegree 2)
    (s₁ s₂:Finset I) (hs:Disjoint s₁ s₂) (u v:I→V) (P:∀i,F.Walk (u i) (v i))
    (hp:∀i∈s₁∪s₂,(P i).IsPath)
    (hP:(↑(s₁∪s₂):Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset))
    (c d:ℕ) (hc:0<c) (hd:0<d) (hlen:∀i∈s₁∪s₂,(P i).length=c*d+4)
    (T:I→Finset ℕ) (hT:∀i∈s₂,T i⊆Finset.range d)
    (t:Finset J) (root:J→V) (C:∀j,F.Walk (root j) (root j))
    (hcycle:∀j∈t,(C j).IsCycle)
    (hC:(↑t:Set J).PairwiseDisjoint (fun j=>(C j).support.toFinset))
    (hcross:∀i∈s₁∪s₂,∀j∈t,Disjoint (P i).support.toFinset (C j).support.toFinset):
    let Z:=DeletedPathIndex s₁ s₂ d T
    let U:Z→V:=deletedPathStart F s₁ s₂ u v P c d T
    let W:Z→V:=deletedPathEnd F s₁ s₂ u v P c d T
    let paths:∀z:Z,F.Walk (U z) (W z):=deletedPathWalk F s₁ s₂ u v P c d T hT
    let deletedV:=(t.biUnion (fun j=>(C j).support.toFinset)) ∪
      (Finset.univ.biUnion (fun z=>(paths z).support.toFinset \ {U z,W z}))
    let deletedE:=(t.biUnion (fun j=>(C j).edges.toFinset)) ∪
      (Finset.univ.biUnion (fun z=>(paths z).edges.toFinset))
    let Q:=F.deleteEdges (deletedE:Set (Sym2 V));
    Q.edgeFinset.card+s₁.card+(∑i∈s₂,(selectedSegmentRuns d (T i)).card)=
      (Finset.univ\deletedV).card ∧ ∀x∈deletedV,∀y,¬Q.Adj x y := by
  let Z:=DeletedPathIndex s₁ s₂ d T
  let U:Z→V:=deletedPathStart F s₁ s₂ u v P c d T
  let W:Z→V:=deletedPathEnd F s₁ s₂ u v P c d T
  let paths:∀z:Z,F.Walk (U z) (W z):=deletedPathWalk F s₁ s₂ u v P c d T hT
  have hprops:=deleted_path_family_properties F s₁ s₂ u v P hp c d hc hd hlen T hT
  have hdisj:(↑(Finset.univ:Finset Z):Set Z).PairwiseDisjoint (fun z=>(paths z).support.toFinset) := by
    intro z _ w _ hne
    exact deleted_path_family_vertex_disjoint F s₁ s₂ hs u v P hp hP c d hc hlen T hT z w hne
  have hcross':∀z∈(Finset.univ:Finset Z),∀j∈t,Disjoint (paths z).support.toFinset (C j).support.toFinset := by
    intro z _ j hj
    exact (hcross (deletedPathParent z) (deleted_path_parent_mem z) j hj).mono
      (deleted_path_support_subset_parent F s₁ s₂ u v P c d hlen T hT z) (by intro x hx;exact hx)
  have hres:=two_factor_residual_graph_after_disjoint_deletions F hF (Finset.univ:Finset Z) U W paths
    (by intro z _;exact (hprops z).1) (by intro z _;exact (hprops z).2) hdisj t root C hcycle hC hcross'
  have hcard:(Finset.univ:Finset Z).card=s₁.card+∑i∈s₂,(selectedSegmentRuns d (T i)).card := by
    rw [Finset.card_univ,deleted_path_index_card]
  dsimp only at hres ⊢
  rw [hcard] at hres
  dsimp only [Z,U,W,paths] at hres ⊢
  exact ⟨by omega,hres.2⟩
end Oberwolfach
