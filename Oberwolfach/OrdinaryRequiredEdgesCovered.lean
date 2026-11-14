module

public import Oberwolfach.OrdinaryProtectedRequiredEdges
public import Oberwolfach.OrdinaryComplementRemainderDecomposition

@[expose] public section
/-! Required physical rim edges covered by the residual placements lie in
the embedded complements, forcing a reference-only terminal rim. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_required_edges_covered_by_complements {n q:ℕ}
    (G:SimpleGraph (Fin n)) (Fs:Fin q→SimpleGraph (Fin n))
    (C:∀u,Finset (Fs u).ConnectedComponent)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (Old E:Fin q→Finset (Sym2 (Fin n)))
    (hpartition:∀u,(((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).edgeFinset).image
      (Sym2.map (f u))=Old u∪E u)
    (hcover:∀e∈G.edgeFinset,∃u,e∈E u):
    G≤ordinaryEmbeddedComplements Fs C f:=by
  intro v w hvw
  have hvw':s(v,w)∈G.edgeFinset:=SimpleGraph.mem_edgeFinset.mpr hvw
  obtain ⟨u,hu⟩:=hcover _ hvw'
  have hh:s(v,w)∈(((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).edgeFinset).image
      (Sym2.map (f u)):=by rw [hpartition u];exact Finset.mem_union_right _ hu
  have hm:s(v,w)∈(((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).map (f u)).edgeFinset:=by
    rw [SimpleGraph.edgeFinset_map]
    obtain ⟨e,he,hEq⟩:=Finset.mem_image.mp hh
    apply Finset.mem_map.mpr
    refine ⟨e,he,?_⟩
    simpa only [Function.Embedding.sym2Map_apply] using hEq
  exact (le_iSup (fun u=>((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).map (f u)) u)
    (SimpleGraph.mem_edgeFinset.mp hm)

theorem ordinary_required_cover_forces_reference_inner
    {V:Type} [Fintype V] [DecidableEq V]
    (Target Sample Reference Protect Embedded:SimpleGraph V) (Inner:Finset V)
    (hRef:Reference≤Sample) (hProtect:Protect≤Reference)
    (hcover:ordinaryProtectedRequired Target Sample Reference Inner≤Embedded):
    ∀v∈Inner,∀w∈Inner,(Target\Embedded).Adj v w→Reference.Adj v w:=by
  intro v hv w hw he
  have hh:=ordinary_protected_required_edges_relations Target Sample Reference Protect Inner hRef hProtect
  apply hh.2.2.1 v hv w hw
  exact ⟨he.1,fun hg=>he.2 (hcover hg)⟩
end Oberwolfach
