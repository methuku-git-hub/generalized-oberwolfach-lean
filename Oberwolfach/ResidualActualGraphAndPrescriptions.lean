module

public import Oberwolfach.ResidualDeletedVertexSetIdentity
public import Oberwolfach.ResidualActualPrescribedSet

@[expose] public section
/-! Combine the actual residual graph and its prescribed set on the same
vertex deletion, keeping the exact count and independence conclusions. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V I J:Type} [Fintype V] [DecidableEq V] [DecidableEq I] [DecidableEq J]

theorem residual_actual_graph_and_prescriptions (F:SimpleGraph V) (hF:F.IsRegularOfDegree 2)
    (s₁ s₂:Finset I) (hs:Disjoint s₁ s₂) (u v:I→V) (P:∀i,F.Walk (u i) (v i))
    (hp:∀i∈s₁∪s₂,(P i).IsPath)
    (hP:(↑(s₁∪s₂):Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset))
    (c d:ℕ) (hc:3≤c) (hd:0<d) (hlen:∀i∈s₁∪s₂,(P i).length=c*d+4)
    (T:I→Finset ℕ) (hT:∀i,T i⊆Finset.range d)
    (t:Finset J) (root:J→V) (C:∀j,F.Walk (root j) (root j))
    (hcycle:∀j∈t,(C j).IsCycle)
    (hC:(↑t:Set J).PairwiseDisjoint (fun j=>(C j).support.toFinset))
    (hcross:∀i∈s₁∪s₂,∀j∈t,Disjoint (P i).support.toFinset (C j).support.toFinset):
    let Z:=DeletedPathIndex s₁ s₂ d T
    let U:Z→V:=deletedPathStart F s₁ s₂ u v P c d T
    let W:Z→V:=deletedPathEnd F s₁ s₂ u v P c d T
    let paths:∀z:Z,F.Walk (U z) (W z):=deletedPathWalk F s₁ s₂ u v P c d T (fun i _=>hT i)
    let deletedV:=(t.biUnion (fun j=>(C j).support.toFinset)) ∪
      (Finset.univ.biUnion (fun z=>(paths z).support.toFinset \ {U z,W z}))
    let deletedE:=(t.biUnion (fun j=>(C j).edges.toFinset)) ∪
      (Finset.univ.biUnion (fun z=>(paths z).edges.toFinset))
    let Q:=F.deleteEdges (deletedE:Set (Sym2 V))
    let R:=Finset.univ\deletedV
    let A₀ := (s₁.biUnion (fun i=>{(P i).getVert 2,(P i).getVert (2+c*d)})) ∪
      (R ∩ s₂.biUnion (fun i=>(Finset.range (d+1)).image (fun j=>(P i).getVert (2+c*j))))
    let missing:=∑i∈s₂,(d-(T i).card)
    let runs:=∑i∈s₂,(selectedSegmentRuns d (T i)).card;
    A₀⊆R ∧ (∀ x∈A₀,∀y∈A₀,¬Q.Adj x y) ∧
      A₀.card=2*s₁.card+s₂.card+missing+runs ∧
      Q.edgeFinset.card+s₁.card+runs=R.card ∧
      R.card≤Q.edgeFinset.card+A₀.card ∧
      ∀ x∈deletedV,∀y,¬Q.Adj x y := by
  let Z:=DeletedPathIndex s₁ s₂ d T
  let U:Z→V:=deletedPathStart F s₁ s₂ u v P c d T
  let W:Z→V:=deletedPathEnd F s₁ s₂ u v P c d T
  let paths:∀z:Z,F.Walk (U z) (W z):=deletedPathWalk F s₁ s₂ u v P c d T (fun i _=>hT i)
  let Cset:=t.biUnion (fun j=>(C j).support.toFinset)
  let deletedV:=Cset∪Finset.univ.biUnion (fun z=>(paths z).support.toFinset \ {U z,W z})
  let deletedE:=(t.biUnion (fun j=>(C j).edges.toFinset)) ∪ Finset.univ.biUnion (fun z=>(paths z).edges.toFinset)
  let Q:=F.deleteEdges (deletedE:Set (Sym2 V))
  let R:=Finset.univ\deletedV
  have hCset:∀i∈s₁∪s₂,Disjoint (P i).support.toFinset Cset := by
    intro i hi
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨j,hj,hxj⟩:=Finset.mem_biUnion.mp hy
    exact Finset.disjoint_left.mp (hcross i hi j hj) hx hxj
  have hid:=deleted_path_family_interiors_identity F s₁ s₂ hs u v P c d T hT
  have hr:=residual_graph_for_actual_path_family F hF s₁ s₂ hs u v P hp hP c d (by omega) hd hlen T
    (by intro i hi;exact hT i) t root C hcycle hC hcross
  have ha:=residual_actual_prescribed_set F Q hF (F.deleteEdges_le _) s₁ s₂ hs u v P hp hP c d hc hd hlen T hT Cset hCset
  have hsum:=(maximal_run_family_counts s₂ d hd T (by intro i hi;exact hT i)).2.1
  dsimp only at hid hr ha hsum ⊢
  dsimp only [Z,U,W,paths,Cset,deletedV,deletedE,Q,R] at hid hr ha ⊢
  rw [hid] at hr ⊢
  refine ⟨ha.1,ha.2.1,ha.2.2,hr.1,?_,hr.2⟩
  omega
end Oberwolfach
