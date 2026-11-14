module

public import Oberwolfach.PrescribedDependentSourcePieces
public import Oberwolfach.PrescribedPieceSourceModel

@[expose] public section
/-! Source vertex sets and arcs are unchanged by the dependent-sum
relabelling of separately typed factors. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I:Type} [Fintype I] [DecidableEq I] {X:I→Type} [∀ i,Fintype (X i)] [∀ i,DecidableEq (X i)]

def prescribedDependentVertices (pieces:∀ i,List (PrescribedSourcePiece (X i))) (i:I):Finset (X i):=
  Finset.univ.filter (fun x=>∃ p∈pieces i,x∈p.vertices)

def prescribedDependentDigraph (pieces:∀ i,List (PrescribedSourcePiece (X i))) (i:I) (x y:X i):Prop:=
  ∃ p∈pieces i,(x,y)∈p.arcs

theorem prescribed_lifted_source_vertex_membership (pieces:∀ i,List (PrescribedSourcePiece (X i)))
    (i:I) (x:X i):
    Sigma.mk i x∈prescribedSourceVertices (prescribedLiftDependentPieces Finset.univ.toList pieces) i ↔
      x∈prescribedDependentVertices pieces i := by
  rw [prescribed_source_model_vertices]
  simp only [prescribedDependentVertices,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨p,hp,hpi,hx⟩
    obtain ⟨j,hj,hp⟩:=List.mem_flatMap.mp hp
    obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp
    simp only at hpi
    subst j
    rw [prescribed_piece_map_vertices] at hx
    obtain ⟨z,hz,hzx⟩:=List.mem_map.mp hx
    have hzx':z=x:=sigma_mk_injective hzx
    subst z
    exact ⟨q,hq,hz⟩
  · rintro ⟨q,hq,hx⟩
    refine ⟨(i,q.map (Sigma.mk i)),?_,rfl,?_⟩
    · apply List.mem_flatMap.mpr
      exact ⟨i,by simp,List.mem_map.mpr ⟨q,hq,rfl⟩⟩
    · rw [prescribed_piece_map_vertices]
      exact List.mem_map.mpr ⟨x,hx,rfl⟩

theorem prescribed_lifted_source_arc_membership (pieces:∀ i,List (PrescribedSourcePiece (X i)))
    (i:I) (x y:X i):
    prescribedSourceDigraph (prescribedLiftDependentPieces Finset.univ.toList pieces) i (Sigma.mk i x) (Sigma.mk i y) ↔
      prescribedDependentDigraph pieces i x y := by
  constructor
  · rintro ⟨p,hp,hpi,he⟩
    obtain ⟨j,hj,hp⟩:=List.mem_flatMap.mp hp
    obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp
    simp only at hpi
    subst j
    rw [prescribed_piece_map_arcs] at he
    obtain ⟨e,he,heq⟩:=Finset.mem_image.mp he
    rcases e with ⟨u,v⟩
    have hu:u=x:=sigma_mk_injective (Prod.mk.inj heq).1
    have hv:v=y:=sigma_mk_injective (Prod.mk.inj heq).2
    subst u;subst v
    exact ⟨q,hq,he⟩
  · rintro ⟨q,hq,he⟩
    refine ⟨(i,q.map (Sigma.mk i)),?_,rfl,?_⟩
    · apply List.mem_flatMap.mpr
      exact ⟨i,by simp,List.mem_map.mpr ⟨q,hq,rfl⟩⟩
    · rw [prescribed_piece_map_arcs]
      exact Finset.mem_image.mpr ⟨(x,y),he,rfl⟩
theorem prescribed_lifted_source_vertex_fiber (pieces:∀ i,List (PrescribedSourcePiece (X i)))
    (i:I) (z:Σ i,X i)
    (hz:z∈prescribedSourceVertices (prescribedLiftDependentPieces Finset.univ.toList pieces) i):
    z.1=i := by
  obtain ⟨p,hp,hpi,hz⟩:=(prescribed_source_model_vertices _ _ _).mp hz
  obtain ⟨j,hj,hp⟩:=List.mem_flatMap.mp hp
  obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp
  simp only at hpi
  subst j
  rw [prescribed_piece_map_vertices] at hz
  obtain ⟨x,hx,heq⟩:=List.mem_map.mp hz
  rw [←heq]

theorem prescribed_lifted_source_vertices (pieces:∀ i,List (PrescribedSourcePiece (X i)))
    (i:I):
    prescribedSourceVertices (prescribedLiftDependentPieces Finset.univ.toList pieces) i =
      (prescribedDependentVertices pieces i).image (Sigma.mk i) := by
  ext z
  rcases z with ⟨j,x⟩
  by_cases hji:j=i
  · subst j
    rw [prescribed_lifted_source_vertex_membership]
    constructor
    · intro hx;exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
    · intro hx
      obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hx
      have h:y=x:=sigma_mk_injective he
      simpa [h] using hy
  · constructor
    · intro hz;exact (hji (prescribed_lifted_source_vertex_fiber pieces i ⟨j,x⟩ hz)).elim
    · intro hz
      obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hz
      have hh:i=j:=congrArg Sigma.fst he
      exact (hji hh.symm).elim

theorem prescribed_lifted_source_vertex_card (pieces:∀ i,List (PrescribedSourcePiece (X i))) (i:I):
    (prescribedSourceVertices (prescribedLiftDependentPieces Finset.univ.toList pieces) i).card =
      (prescribedDependentVertices pieces i).card := by
  rw [prescribed_lifted_source_vertices]
  exact Finset.card_image_of_injective _ sigma_mk_injective
end Oberwolfach
