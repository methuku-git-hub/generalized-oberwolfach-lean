module

public import Oberwolfach.ResidualActualPhysicalEdges

@[expose] public section
/-! Physical rim-edge packing across hubs implies exactly the symmetric-edge
packing hypotheses used by the residual degree theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem physical_cover_gives_symmetric_old_edge_cover
    {X V K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (Final:Finset (Sym2 X)) (ψ:X→V) (D:X→X→Prop)
    (horient:∀x y,G.Adj x y→D x y ∨ D y x) (Pack:Finset (Finset V))
    (hcover:∀x y,s(x,y)∈data.deletedEdges\Final→D x y→{ψ x,ψ y}∈Pack):
    ∀e∈(data.deletedEdges\Final).image (Sym2.map ψ),e.toFinset∈Pack:=by
  intro e he
  obtain ⟨f,hf,rfl⟩:=Finset.mem_image.mp he
  induction f using Sym2.ind with
  | _ x y =>
    have hadj:G.Adj x y:=SimpleGraph.mem_edgeFinset.mp (data.deleted_edges_subset_factor (Finset.mem_sdiff.mp hf).1)
    rcases horient x y hadj with hxy|hyx
    · simpa only [Sym2.map_mk,Sym2.toFinset_mk_eq] using hcover x y hf hxy
    · have hf':s(y,x)∈data.deletedEdges\Final:=by simpa only [Sym2.eq_swap] using hf
      have hh:=hcover y x hf' hyx
      simpa only [Sym2.map_mk,Sym2.toFinset_mk_eq,Finset.pair_comm] using hh

theorem physical_disjointness_gives_symmetric_packing
    {U V:Type} [Fintype U] [Fintype V] [DecidableEq V]
    (old:U→Finset (Sym2 V)) (physical:U→Finset (Finset V))
    (hcover:∀w e,e∈old w→e.toFinset∈physical w)
    (hdis:∀w z,w≠z→Disjoint (physical w) (physical z)):
    ∃Pack:Finset (Sym2 V),
      (∀w z,w≠z→Disjoint (old w) (old z)) ∧ (∀w,old w⊆Pack):=by
  let Pack:Finset (Sym2 V):=Finset.univ.filter (fun e=>e.toFinset∈Finset.univ.biUnion physical)
  refine ⟨Pack,?_,?_⟩
  · intro w z hne
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact Finset.disjoint_left.mp (hdis w z hne) (hcover w e he) (hcover z e hf)
  · intro w e he
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨w,Finset.mem_univ _,hcover w e he⟩⟩
end Oberwolfach
