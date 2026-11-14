module

public import Oberwolfach.ResidualSelectedRunOverlap
public import Oberwolfach.ResidualActualGraphAndPrescriptions

@[expose] public section
/-! In the actual deletion construction, the old embedded domain and the
surviving source vertices meet exactly at the prescribed set. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I J:Type} [Fintype V] [DecidableEq V] [DecidableEq I] [DecidableEq J]

theorem residual_actual_embedding_overlap (F:SimpleGraph V) (hF:F.IsRegularOfDegree 2)
    (s₁ s₂:Finset I) (hs:Disjoint s₁ s₂) (u v:I→V) (P:∀i,F.Walk (u i) (v i))
    (hp:∀i∈s₁∪s₂,(P i).IsPath)
    (hP:(↑(s₁∪s₂):Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset))
    (c d:ℕ) (hc:3≤c) (hd:0<d) (hlen:∀i∈s₁∪s₂,(P i).length=c*d+4)
    (T:I→Finset ℕ) (hT:∀i,T i⊆Finset.range d)
    (t:Finset J) (root:J→V) (C:∀j,F.Walk (root j) (root j))
    (hcycle:∀j∈t,(C j).IsCycle)
    (hC:(↑t:Set J).PairwiseDisjoint (fun j=>(C j).support.toFinset))
    (hcross:∀i∈s₁∪s₂,∀j∈t,Disjoint (P i).support.toFinset (C j).support.toFinset)
    (Cembed:Finset V) (hEmbed:Cembed⊆t.biUnion (fun j=>(C j).support.toFinset)):
    let Z:=DeletedPathIndex s₁ s₂ d T
    let U:Z→V:=deletedPathStart F s₁ s₂ u v P c d T
    let W:Z→V:=deletedPathEnd F s₁ s₂ u v P c d T
    let paths:∀z:Z,F.Walk (U z) (W z):=deletedPathWalk F s₁ s₂ u v P c d T (fun i _=>hT i)
    let R:=Finset.univ \ ((t.biUnion (fun j=>(C j).support.toFinset)) ∪
      Finset.univ.biUnion (fun z=>(paths z).support.toFinset \ {U z,W z}))
    let A₀ := (s₁.biUnion (fun i=>{(P i).getVert 2,(P i).getVert (2+c*d)})) ∪
      (R ∩ s₂.biUnion (fun i=>(Finset.range (d+1)).image (fun j=>(P i).getVert (2+c*j))))
    let X:=A₀ ∪ (Finset.univ.biUnion (fun r:SelectedRunIndex s₂ d T=>(paths (.inr r)).support.toFinset)) ∪ Cembed;
    X∩R=A₀ := by
  have ha:=residual_actual_graph_and_prescriptions F hF s₁ s₂ hs u v P hp hP c d hc hd hlen T hT t root C hcycle hC hcross
  have hh:=residual_selected_run_overlap F s₁ s₂ u v P c d T (fun i _=>hT i)
    (t.biUnion (fun j=>(C j).support.toFinset)) Cembed hEmbed
  dsimp only at ha hh ⊢
  exact hh ha.1
end Oberwolfach
