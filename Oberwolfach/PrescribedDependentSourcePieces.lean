module

public import Oberwolfach.PrescribedSourcePieceMap
public import Oberwolfach.PrescribedSourceFamilyInduction

@[expose] public section
/-! Independent source vertex types can be embedded in a common dependent
sum without introducing intersections between factors. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I:Type} [Fintype I] [DecidableEq I] {X:I→Type} [∀ i,DecidableEq (X i)]

def prescribedLiftDependentPieces (is:List I) (pieces:∀ i,List (PrescribedSourcePiece (X i))):
    List (I×PrescribedSourcePiece (Σ i,X i)):=
  is.flatMap (fun i=>(pieces i).map (fun p=>(i,p.map (Sigma.mk i))))

theorem prescribed_lifted_pieces_apart (pieces:∀ i,List (PrescribedSourcePiece (X i)))
    (hapart:∀ i,(pieces i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset)):
    ∀ is:List I,is.Nodup→(prescribedLiftDependentPieces is pieces).Pairwise PrescribedPiecesApart := by
  intro is
  induction is with
  | nil => intro hn;simp [prescribedLiftDependentPieces]
  | cons i is ih =>
    intro hn
    have hn':=List.nodup_cons.mp hn
    simp only [prescribedLiftDependentPieces,List.flatMap_cons,List.pairwise_append]
    refine ⟨?_,ih hn'.2,?_⟩
    · rw [List.pairwise_map]
      apply (hapart i).imp
      intro p q h
      right
      simp only [prescribed_piece_map_vertices]
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      obtain ⟨a,ha,haz⟩:=List.mem_map.mp (List.mem_toFinset.mp hz)
      obtain ⟨b,hb,hbz⟩:=List.mem_map.mp (List.mem_toFinset.mp hz')
      have hab:a=b:=sigma_mk_injective (haz.trans hbz.symm)
      subst b
      exact (Finset.disjoint_left.mp h (List.mem_toFinset.mpr ha)) (List.mem_toFinset.mpr hb)
    · intro p hp q hq
      obtain ⟨p',hp',rfl⟩:=List.mem_map.mp hp
      obtain ⟨j,hj,hq⟩:=List.mem_flatMap.mp hq
      obtain ⟨q',hq',rfl⟩:=List.mem_map.mp hq
      left
      intro h
      have hij:i=j:=h
      subst j
      exact hn'.1 hj

theorem prescribed_lifted_pieces_shape (pieces:∀ i,List (PrescribedSourcePiece (X i)))
    (hshape:∀ i p,p∈pieces i→p.Shape) (is:List I):
    ∀ p∈prescribedLiftDependentPieces is pieces,p.2.Shape := by
  intro p hp
  obtain ⟨i,hi,hp⟩:=List.mem_flatMap.mp hp
  obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp
  apply prescribed_piece_map_shape (Sigma.mk i) ?_ q (hshape i q hq)
  intro a b hab
  exact sigma_mk_injective hab
end Oberwolfach
