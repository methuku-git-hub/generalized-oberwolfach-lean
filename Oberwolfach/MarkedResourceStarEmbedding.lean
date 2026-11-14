module

public import Oberwolfach.MarkedResourceEmbeddingGeometry

@[expose] public section

/-! Protected stars commute with the actual embeddings of the nested
row and hub domains. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' : Type} [DecidableEq V] [DecidableEq U]
    [DecidableEq V'] [DecidableEq U']

theorem markedResourceEmbedding_star_iff (f : V↪V') (g : U↪U')
    (A : Finset V) (B : Finset U) (I : Finset V') (J : Finset U')
    (hA : ∀ x,f x∈I↔x∈A) (hB : ∀ u,g u∈J↔u∈B)
    (e : Finset V⊕(V×U)) :
    markedStarResource I J (markedResourceEmbedding f g e)↔markedStarResource A B e := by
  cases e with
  | inl e =>
    change (∃ x∈e.image f,x∈I)↔∃ x∈e,x∈A
    constructor
    · rintro ⟨y,hy,hi⟩
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact ⟨x,hx,(hA x).mp hi⟩
    · rintro ⟨x,hx,ha⟩
      exact ⟨f x,Finset.mem_image.mpr ⟨x,hx,rfl⟩,(hA x).mpr ha⟩
  | inr z => exact or_congr (hA z.1) (hB z.2)

theorem markedResourceEmbedding_star_filter (f : V↪V') (g : U↪U')
    (A : Finset V) (B : Finset U) (I : Finset V') (J : Finset U')
    (hA : ∀ x,f x∈I↔x∈A) (hB : ∀ u,g u∈J↔u∈B)
    (S : Finset (Finset V⊕(V×U))) :
    (S.image (markedResourceEmbedding f g)).filter (markedStarResource I J)=
      (S.filter (markedStarResource A B)).image (markedResourceEmbedding f g) := by
  rw [Finset.filter_image]
  congr 1
  ext e
  simp only [Finset.mem_filter,markedResourceEmbedding_star_iff f g A B I J hA hB]

end Oberwolfach
