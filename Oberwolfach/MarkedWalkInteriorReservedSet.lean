module

public import Oberwolfach.DisjointSequenceInteriorCover
public import Oberwolfach.SimpleWalkLengthEndpoints

@[expose] public section
/-! The checked marked-walk coverage puts strict source-path interior images
in the residual marked spoke set, with the same endpoint witnesses. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_marked_walk_interiors_in_reserved
    {X V I:Type*} [DecidableEq X] [DecidableEq V] [Fintype I]
    (G:SimpleGraph V) (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X)
    (g:{x // x∈bufferedPathFullDomain n inner}↪V)
    (a b:I→V) (q:∀i,G.Walk (a i) (b i))
    (hpath:∀i,(q i).IsPath) (hlen:∀i,(q i).length=n i)
    (hmatch:∀i p,g ⟨inner i p,buffered_path_vertex_mem_domain n inner i p⟩=
      simpleWalkLengthEmbedding G (q i) (hpath i) (n i) (hlen i) p)
    (hdis:∀i j,i≠j→Disjoint (q i).support.toFinset (q j).support.toFinset)
    (R:Finset V)
    (hcover:Finset.univ.biUnion (fun i=>(q i).support.toFinset)=
      R ∪ Finset.univ.image b) :
    ∀x (hx:x∈bufferedPathStrictInterior n inner),
      g ⟨x,buffered_strict_interior_subset_domain n inner hx⟩∈R := by
  let f:∀i,Fin (n i+1)↪V:=fun i=>simpleWalkLengthEmbedding G (q i) (hpath i) (n i) (hlen i)
  have hfdis:∀i j,i≠j→Disjoint (Finset.univ.image (f i)) (Finset.univ.image (f j)):=by
    intro i j hij
    rw [simple_walk_length_embedding_support,simple_walk_length_embedding_support]
    exact hdis i j hij
  have hfcover:Finset.univ.biUnion (fun i=>Finset.univ.image (f i)) =
      R ∪ Finset.univ.image (fun i=>f i (Fin.last (n i))):=by
    have hsupp:(fun i=>Finset.univ.image (f i))=(fun i=>(q i).support.toFinset):=by
      funext i
      exact simple_walk_length_embedding_support G (q i) (hpath i) (n i) (hlen i)
    rw [hsupp]
    have he:(fun i=>f i (Fin.last (n i)))=b:=by
      funext i
      exact (simple_walk_length_embedding_endpoints G (q i) (hpath i) (n i) (hlen i)).2
    rw [he]
    exact hcover
  exact buffered_strict_map_inside_reserved n inner g f R hmatch hfdis hfcover
end Oberwolfach
