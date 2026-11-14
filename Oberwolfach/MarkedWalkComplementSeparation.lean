module

public import Oberwolfach.MarkedWalkInteriorReservedSet
public import Oberwolfach.InteriorImageSeparation

@[expose] public section
/-! Derive the final within-factor image separation from reconstructed walk
coverage, endpoint agreement, and disjoint residual spoke/complement sets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_walk_complement_image_separation
    {X V I:Type*} [DecidableEq X] [DecidableEq V] [Fintype I]
    (G:SimpleGraph V) (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X)
    (g:{x // x∈bufferedPathFullDomain n inner}↪V)
    (fC:{x // x∉bufferedPathStrictInterior n inner}→V)
    (a b:I→V) (q:∀i,G.Walk (a i) (b i))
    (hpath:∀i,(q i).IsPath) (hlen:∀i,(q i).length=n i)
    (hmatch:∀i p,g ⟨inner i p,buffered_path_vertex_mem_domain n inner i p⟩=
      simpleWalkLengthEmbedding G (q i) (hpath i) (n i) (hlen i) p)
    (hwalkDis:∀i j,i≠j→Disjoint (q i).support.toFinset (q j).support.toFinset)
    (R Z:Finset V) (hRZ:Disjoint R Z)
    (hcover:Finset.univ.biUnion (fun i=>(q i).support.toFinset)=R ∪ Finset.univ.image b)
    (hend:∀i (p:Fin (n i+1)),(p=0 ∨ p=Fin.last (n i))→
      ∀hpD:inner i p∉bufferedPathStrictInterior n inner,
      g ⟨inner i p,buffered_path_vertex_mem_domain n inner i p⟩=fC ⟨inner i p,hpD⟩)
    (hZ:∀x (hx:x∉bufferedPathStrictInterior n inner),x∉bufferedPathFullDomain n inner→fC ⟨x,hx⟩∈Z) :
    ∀x (hx:x∈bufferedPathStrictInterior n inner) y (hy:y∉bufferedPathStrictInterior n inner),
      g ⟨x,buffered_strict_interior_subset_domain n inner hx⟩≠fC ⟨y,hy⟩ := by
  have hbound:∀x (hx:x∈bufferedPathFullDomain n inner) (hxD:x∉bufferedPathStrictInterior n inner),
      g ⟨x,hx⟩=fC ⟨x,hxD⟩:=by
    intro x hx hxD
    obtain ⟨i,hi|hi⟩:=buffered_path_boundary_is_endpoint n inner x hx hxD
    · subst x
      exact hend i 0 (Or.inl rfl) hxD
    · subst x
      exact hend i (Fin.last (n i)) (Or.inr rfl) hxD
  have hinside:=buffered_marked_walk_interiors_in_reserved G n inner g a b q hpath hlen hmatch hwalkDis R hcover
  apply interior_image_separated_by_boundary_and_avoidance
    (bufferedPathFullDomain n inner) (bufferedPathStrictInterior n inner)
    (buffered_strict_interior_subset_domain n inner) R g fC hbound hinside
  intro x hx hxA hmem
  exact (Finset.disjoint_left.mp hRZ) hmem (hZ x hx hxA)
end Oberwolfach
