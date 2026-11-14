module

public import Oberwolfach.BufferedPathInteriorCompletion
public import Oberwolfach.PartialEmbeddingPhysicalEdgeUnion

@[expose] public section
/-! Restrict an all-interval path map to the selected final intervals,
without adding their approximate-interval interiors to the deleted set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def bufferedSelectedLengths {I:Type*} (S:Finset I) (n:I→ℕ) : {i // i∈S}→ℕ := fun i=>n i.val

def bufferedSelectedPaths {X I:Type*} (S:Finset I) (n:I→ℕ)
    (inner:∀i,Fin (n i+1)↪X) : ∀i:{i // i∈S},Fin (bufferedSelectedLengths S n i+1)↪X :=
  fun i=>inner i.val

theorem buffered_selected_domain_subset
    {X I:Type*} [Fintype I] [DecidableEq I] [DecidableEq X]
    (S:Finset I) (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X) :
    bufferedPathFullDomain (bufferedSelectedLengths S n) (bufferedSelectedPaths S n inner) ⊆
      bufferedPathFullDomain n inner := by
  classical
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨i,_,hi⟩
  rcases Finset.mem_image.mp hi with ⟨p,_,rfl⟩
  exact Finset.mem_biUnion.mpr ⟨i.val,Finset.mem_univ _,Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩⟩

def finsetSubsetEmbedding {X:Type*} [DecidableEq X] {A B:Finset X} (h:A⊆B) :
    {x // x∈A}↪{x // x∈B} where
  toFun x:=⟨x.val,h x.property⟩
  inj' := by intro x y hxy;apply Subtype.ext;exact congrArg (fun z:{x // x∈B}=>z.val) hxy

theorem partial_factor_physical_edges_restrict
    {X Y:Type*} [DecidableEq X] (G:SimpleGraph X) {A B:Finset X} (h:A⊆B)
    (f:{x // x∈B}→Y) :
    partialFactorPhysicalEdgesPoly {x // x∈A} (G.induce (↑A:Set X)) (fun x=>f (finsetSubsetEmbedding h x)) ⊆
      partialFactorPhysicalEdgesPoly {x // x∈B} (G.induce (↑B:Set X)) f := by
  intro e he
  obtain ⟨x,y,hxy,rfl⟩:=he
  exact ⟨finsetSubsetEmbedding h x,finsetSubsetEmbedding h y,hxy,rfl⟩

def restrictBufferedPathMap
    {X Y I:Type*} [Fintype I] [DecidableEq I] [DecidableEq X]
    (S:Finset I) (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X)
    (f:{x // x∈bufferedPathFullDomain n inner}↪Y) :
    {x // x∈bufferedPathFullDomain (bufferedSelectedLengths S n) (bufferedSelectedPaths S n inner)}↪Y :=
  (finsetSubsetEmbedding (buffered_selected_domain_subset S n inner)).trans f

theorem selected_buffered_path_map_graph_and_edges
    {X Y I:Type*} [Fintype I] [DecidableEq I] [DecidableEq X]
    (G:SimpleGraph X) (H:SimpleGraph Y) (S:Finset I) (n:I→ℕ)
    (inner:∀i,Fin (n i+1)↪X) (f:{x // x∈bufferedPathFullDomain n inner}↪Y)
    (hgraph:∀x y,G.Adj x.val y.val→H.Adj (f x) (f y)) :
    (∀x y,G.Adj x.val y.val→H.Adj (restrictBufferedPathMap S n inner f x) (restrictBufferedPathMap S n inner f y)) ∧
    partialFactorPhysicalEdgesPoly
      {x // x∈bufferedPathFullDomain (bufferedSelectedLengths S n) (bufferedSelectedPaths S n inner)}
      (G.induce (↑(bufferedPathFullDomain (bufferedSelectedLengths S n) (bufferedSelectedPaths S n inner)):Set X))
      (restrictBufferedPathMap S n inner f) ⊆
    partialFactorPhysicalEdgesPoly {x // x∈bufferedPathFullDomain n inner}
      (G.induce (↑(bufferedPathFullDomain n inner):Set X)) f := by
  constructor
  · intro x y hxy
    exact hgraph (finsetSubsetEmbedding (buffered_selected_domain_subset S n inner) x)
      (finsetSubsetEmbedding (buffered_selected_domain_subset S n inner) y) hxy
  · exact partial_factor_physical_edges_restrict G (buffered_selected_domain_subset S n inner) f
end Oberwolfach
