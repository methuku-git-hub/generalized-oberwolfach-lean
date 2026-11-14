module

public import Oberwolfach.PrescribedFamilyAvoidOldPacking
public import Oberwolfach.PrescribedFamilyPhysicalDegree

@[expose] public section
/-! A directed source embedding avoids an undirected reserved graph whenever
each permitted directed arc avoids that graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
  {X:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

theorem prescribed_family_avoids_physical_graph
    (pieces:∀i,List (PrescribedSourcePiece (X i))) (Φ:∀i,X i→V)
    (D:V→V→Prop) (R:SimpleGraph V)
    (harc:∀i x y,prescribedDependentDigraph pieces i x y→D (Φ i x) (Φ i y))
    (havoid:∀x y,D x y→¬R.Adj x y):
    let E:=fun i=>((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i))
    ∀x y,(prescribedPhysicalUnion E).Adj x y→¬R.Adj x y:=by
  intro E x y he hr
  have hemem:s(x,y)∈Finset.univ.biUnion E:=by
    have hh:=he
    simp only [prescribedPhysicalUnion,SimpleGraph.fromEdgeSet_adj,Finset.mem_coe] at hh
    exact hh.1
  obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hemem
  obtain ⟨e,he',heq⟩:=Finset.mem_image.mp hi
  induction e using Sym2.ind with
  | _ a b =>
    have hab:(prescribedDependentGraph pieces i).Adj a b:=SimpleGraph.mem_edgeFinset.mp he'
    have hdir:=prescribed_dependent_source_representation pieces i a b hab
    have hp:s(Φ i a,Φ i b)=s(x,y):=by simpa using heq
    have hR:R.Adj (Φ i a) (Φ i b):=by
      have hmem:s(Φ i a,Φ i b)∈R.edgeFinset:=by rw [hp];exact SimpleGraph.mem_edgeFinset.mpr hr
      exact SimpleGraph.mem_edgeFinset.mp hmem
    rcases hdir with h|h
    · exact havoid _ _ (harc i a b h) hR
    · exact havoid _ _ (harc i b a h) hR.symm
end Oberwolfach
