module

public import Oberwolfach.BufferedPathBoundaryCompletion

@[expose] public section
/-! When disjoint reconstructed paths cover a reserved set and their final
endpoints, every nonfinal path vertex lies in the reserved set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem disjoint_sequences_before_last_in_reserved
    {V I:Type*} [DecidableEq V] [Fintype I]
    (n:I→ℕ) (f:∀i,Fin (n i+1)↪V) (R:Finset V)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (f i)) (Finset.univ.image (f j)))
    (hcover:Finset.univ.biUnion (fun i=>Finset.univ.image (f i)) =
      R ∪ Finset.univ.image (fun i=>f i (Fin.last (n i)))) :
    ∀i (p:Fin (n i+1)),p.val<n i→f i p∈R := by
  classical
  intro i p hp
  have hin:f i p∈Finset.univ.biUnion (fun i=>Finset.univ.image (f i)):=
    Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩⟩
  rw [hcover] at hin
  rcases Finset.mem_union.mp hin with hR|hEnd
  · exact hR
  · obtain ⟨j,_,heq⟩:=Finset.mem_image.mp hEnd
    by_cases hij:i=j
    · subst j
      have he:(Fin.last (n i):Fin (n i+1))=p:=(f i).injective heq
      have heval:n i=p.val:=congrArg Fin.val he
      omega
    · have hj:f i p∈Finset.univ.image (f j):=by
        exact Finset.mem_image.mpr ⟨Fin.last (n j),Finset.mem_univ _,heq⟩
      have hi:f i p∈Finset.univ.image (f i):=Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩
      exact (Finset.disjoint_left.mp (hdis i j hij) hi hj).elim

theorem buffered_strict_map_inside_reserved
    {X V I:Type*} [DecidableEq X] [DecidableEq V] [Fintype I]
    (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X)
    (g:{x // x∈bufferedPathFullDomain n inner}↪V)
    (f:∀i,Fin (n i+1)↪V) (R:Finset V)
    (hmatch:∀i p,g ⟨inner i p,buffered_path_vertex_mem_domain n inner i p⟩=f i p)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (f i)) (Finset.univ.image (f j)))
    (hcover:Finset.univ.biUnion (fun i=>Finset.univ.image (f i)) =
      R ∪ Finset.univ.image (fun i=>f i (Fin.last (n i)))) :
    ∀x (hx:x∈bufferedPathStrictInterior n inner),
      g ⟨x,buffered_strict_interior_subset_domain n inner hx⟩∈R := by
  classical
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨i,_,hxi⟩
  rcases Finset.mem_image.mp hxi with ⟨p,hp,rfl⟩
  have hp':=(Finset.mem_filter.mp hp).2
  rw [hmatch i p]
  exact disjoint_sequences_before_last_in_reserved n f R hdis hcover i p hp'.2
end Oberwolfach
