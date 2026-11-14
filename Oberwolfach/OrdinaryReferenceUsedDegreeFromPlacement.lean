module

public import Oberwolfach.OrdinaryComplementRemainderDecomposition
public import Oberwolfach.PrescribedFamilyPhysicalDegree

@[expose] public section
/-! If old matched edges avoid the reference, only the bounded-degree new
placement can consume reference edges in the embedded complements. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reference_used_degree_from_placement {n q:ℕ}
    (Reference:SimpleGraph (Fin n)) (Fs:Fin q→SimpleGraph (Fin n))
    (C:∀u,Finset (Fs u).ConnectedComponent)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (Old New:Fin q→Finset (Sym2 (Fin n)))
    (hpartition:∀u,(((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).edgeFinset).image
      (Sym2.map (f u))=Old u∪New u)
    (hOld:∀u,Disjoint (Old u) Reference.edgeFinset)
    (loss:ℝ) (hNew:∀x,((prescribedPhysicalUnion New).degree x:ℝ)≤loss):
    ∀x,((Reference⊓ordinaryEmbeddedComplements Fs C f).degree x:ℝ)≤loss:=by
  have hsub:Reference⊓ordinaryEmbeddedComplements Fs C f≤prescribedPhysicalUnion New:=by
    intro x y hxy
    obtain ⟨u,hu⟩:=SimpleGraph.iSup_adj.mp hxy.2
    have hm:s(x,y)∈(((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).map (f u)).edgeFinset:=
      SimpleGraph.mem_edgeFinset.mpr hu
    rw [SimpleGraph.edgeFinset_map] at hm
    obtain ⟨e,he,heq⟩:=Finset.mem_map.mp hm
    have he':s(x,y)∈(((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).edgeFinset).image (Sym2.map (f u)):=by
      apply Finset.mem_image.mpr
      exact ⟨e,he,by simpa only [Function.Embedding.sym2Map_apply] using heq⟩
    rw [hpartition u] at he'
    have hRef:s(x,y)∈Reference.edgeFinset:=SimpleGraph.mem_edgeFinset.mpr hxy.1
    have hnew:s(x,y)∈New u:=by
      rcases Finset.mem_union.mp he' with hold|hnew
      · exact False.elim (Finset.disjoint_left.mp (hOld u) hold hRef)
      · exact hnew
    change (SimpleGraph.fromEdgeSet (↑(Finset.univ.biUnion New):Set (Sym2 (Fin n)))).Adj x y
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    exact ⟨Finset.mem_biUnion.mpr ⟨u,Finset.mem_univ _,hnew⟩,hxy.1.ne⟩
  intro x
  have hh:((Reference⊓ordinaryEmbeddedComplements Fs C f).degree x:ℝ)≤(prescribedPhysicalUnion New).degree x:=by
    exact_mod_cast SimpleGraph.degree_le_of_le hsub
  exact hh.trans (hNew x)
end Oberwolfach
