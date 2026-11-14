module

public import Oberwolfach.PrescribedDependentGraphMap

@[expose] public section
/-! Mapping the entire source graph before or after passing to the common
vertex universe gives the same physical edge set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
  {X:I→Type} [∀ i,Fintype (X i)] [∀ i,DecidableEq (X i)]

theorem prescribed_lifted_full_edge_images (pieces:∀ i,List (PrescribedSourcePiece (X i)))
    (f:I→(Σ i,X i)→V) (i:I):
    ((prescribedSourceGraph (prescribedLiftDependentPieces Finset.univ.toList pieces) i).edgeFinset).image (Sym2.map (f i))=
      ((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (fun x=>f i (Sigma.mk i x))) := by
  let G:=prescribedSourceGraph (prescribedLiftDependentPieces Finset.univ.toList pieces) i
  let H:=prescribedDependentGraph pieces i
  let g:X i↪Σ i,X i:=⟨Sigma.mk i,sigma_mk_injective⟩
  have hg:G=H.map g:=prescribed_lifted_source_graph_eq_map pieces i
  have heq:G.edgeSet=g.sym2Map '' H.edgeSet:=by
    rw [hg]
    exact SimpleGraph.edgeSet_map g H
  ext e
  constructor
  · intro he
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp he
    have ha':a∈G.edgeSet:=SimpleGraph.mem_edgeFinset.mp ha
    rw [heq] at ha'
    obtain ⟨b,hb,rfl⟩:=ha'
    apply Finset.mem_image.mpr
    refine ⟨b,SimpleGraph.mem_edgeFinset.mpr hb,?_⟩
    change Sym2.map (fun x:X i=>f i (Sigma.mk i x)) b = Sym2.map (f i) (Sym2.map (Sigma.mk i) b)
    rw [Sym2.map_map]
    rfl
  · intro he
    obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp he
    apply Finset.mem_image.mpr
    refine ⟨g.sym2Map b,?_,?_⟩
    · apply SimpleGraph.mem_edgeFinset.mpr
      rw [heq]
      exact ⟨b,SimpleGraph.mem_edgeFinset.mp hb,rfl⟩
    · change Sym2.map (f i) (Sym2.map (Sigma.mk i) b)=Sym2.map (fun x:X i=>f i (Sigma.mk i x)) b
      rw [Sym2.map_map]
      rfl
end Oberwolfach
