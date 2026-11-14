module

public import Oberwolfach.ActualOldPhysicalCoverage

@[expose] public section
/-! The physical edges used by matched source cycles and selected runs are
contained in any declared coverage pack, so disjoint packs prevent overlap. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def actualOldPhysicalEdges
    {X V K J:Type} [Fintype X] [Fintype K] [Fintype J] [DecidableEq X]
    [DecidableEq K] [DecidableEq J] [DecidableEq V]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F) (ψ:X→V):Finset (Finset V):=
  data.t.biUnion (fun j=>(Finset.range (data.C j).length).image
    (fun k=>{ψ ((data.C j).getVert k),ψ ((data.C j).getVert (k+1))})) ∪
  Finset.univ.biUnion (fun r:SelectedRunIndex data.s₂ data.d data.T=>
    (Finset.range (data.path (.inr r)).length).image
      (fun k=>{ψ ((data.path (.inr r)).getVert k),ψ ((data.path (.inr r)).getVert (k+1))}))

theorem actual_old_physical_edges_subset
    {X V K J:Type} [Fintype X] [Fintype K] [Fintype J] [DecidableEq X]
    [DecidableEq K] [DecidableEq J] [DecidableEq V]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F)
    (ψ:X→V) (Pack:Finset (Finset V)) (h:ActualOldPhysicalCoverage data ψ Pack):
    actualOldPhysicalEdges data ψ⊆Pack:=by
  classical
  intro e he
  simp only [actualOldPhysicalEdges,Finset.mem_union,Finset.mem_biUnion,Finset.mem_univ,
    true_and,Finset.mem_image,Finset.mem_range] at he
  rcases he with ⟨j,hj,k,hk,rfl⟩|⟨r,k,hk,rfl⟩
  · exact h.1 j hj k hk
  · exact h.2 r k hk

theorem actual_old_physical_edges_disjoint
    {X Y V K J K' J':Type} [Fintype X] [Fintype Y] [Fintype K] [Fintype J]
    [Fintype K'] [Fintype J'] [DecidableEq X] [DecidableEq Y] [DecidableEq K]
    [DecidableEq J] [DecidableEq K'] [DecidableEq J'] [DecidableEq V]
    {F:SimpleGraph X} {G:SimpleGraph Y}
    (d:ActualResidualData (K:=K) (J:=J) F) (e:ActualResidualData (K:=K') (J:=J') G)
    (ψ:X→V) (φ:Y→V) (P Q:Finset (Finset V))
    (hP:ActualOldPhysicalCoverage d ψ P) (hQ:ActualOldPhysicalCoverage e φ Q)
    (hPQ:Disjoint P Q):Disjoint (actualOldPhysicalEdges d ψ) (actualOldPhysicalEdges e φ):=
  hPQ.mono (actual_old_physical_edges_subset d ψ P hP) (actual_old_physical_edges_subset e φ Q hQ)
end Oberwolfach
