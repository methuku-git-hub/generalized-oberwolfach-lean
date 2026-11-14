module

public import Oberwolfach.MarkedActiveVertexIncidence
public import Oberwolfach.MarkedResourceStarEmbedding

@[expose] public section

/-! Transport the next fixed-reference error to its actual smaller vertex
types. Both incidence bounds retain their constants, and the deletion is
empty on the next protected inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' E K E' K' : Type}
    [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [Fintype V'] [Fintype U'] [Fintype E'] [Fintype K']
    [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']

theorem marked_reindexed_fixed_remainder
    (tail head : E→V) (ktail khead : K→V)
    (tail' head' : E'→V') (ktail' khead' : K'→V')
    (ρ : Equiv.Perm V) (π : Equiv.Perm V') (f : V↪V') (g : U↪U')
    (hcomm : ∀ v,f (ρ v)=π (f v)) (e : E↪E') (k : K↪K')
    (ht : ∀ a,tail' (e a)=f (tail a)) (hh : ∀ a,head' (e a)=f (head a))
    (hkt : ∀ a,ktail' (k a)=f (ktail a)) (hkh : ∀ a,khead' (k a)=f (khead a))
    (H₀ Hₖ : V→U→Prop) (H₀' Hₖ' : V'→U'→Prop)
    (h₀ : ∀ v u,H₀ v u→H₀' (f v) (g u))
    (hₖ : ∀ v u,Hₖ v u→Hₖ' (f v) (g u))
    (B : Finset (Finset V⊕(V×U))) (F : Finset (Finset V'⊕(V'×U')))
    (hF : F⊆B.image (markedResourceEmbedding f g))
    (A : Finset V) (Z : Finset U) (I : Finset V') (J : Finset U')
    (hA : ∀ x,f x∈I↔x∈A) (hZ : ∀ u,g u∈J↔u∈Z)
    (hInner : F.filter (markedInnerResource I J)=∅)
    (γ σloss : ℝ)
    (hInc : ∀ physical x,(((markedIncidentEdges tail' head' ktail' khead' π H₀' Hₖ' physical x).filter
      (fun a=>markedActivePhysical tail' head' ktail' khead' π H₀' Hₖ' a∈F)).card:ℝ)≤γ)
    (hStar : ∀ physical x,(((markedIncidentEdges tail' head' ktail' khead' π H₀' Hₖ' physical x).filter
      (fun a=>markedActivePhysical tail' head' ktail' khead' π H₀' Hₖ' a∈
        F.filter (markedStarResource I J))).card:ℝ)≤σloss) :
    ∃ F₀⊆B,
      F₀.image (markedResourceEmbedding f g)=F ∧
      (B\F₀).image (markedResourceEmbedding f g)=B.image (markedResourceEmbedding f g)\F ∧
      F₀.filter (markedInnerResource A Z)=∅ ∧
      (∀ physical x,(((markedIncidentEdges tail head ktail khead ρ H₀ Hₖ physical x).filter
        (fun a=>markedActivePhysical tail head ktail khead ρ H₀ Hₖ a∈F₀)).card:ℝ)≤γ) ∧
      (∀ physical x,(((markedIncidentEdges tail head ktail khead ρ H₀ Hₖ physical x).filter
        (fun a=>markedActivePhysical tail head ktail khead ρ H₀ Hₖ a∈
          F₀.filter (markedStarResource A Z))).card:ℝ)≤σloss) := by
  let emb := markedResourceEmbedding f g
  let F₀ := B.filter (fun b=>emb b∈F)
  have hImage : F₀.image emb=F := by
    ext b
    constructor
    · intro hb
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
      exact (Finset.mem_filter.mp ha).2
    · intro hb
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (hF hb)
      exact Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,hb⟩,rfl⟩
  have hStarImage : (F₀.filter (markedStarResource A Z)).image emb=F.filter (markedStarResource I J) := by
    rw [←markedResourceEmbedding_star_filter f g A Z I J hA hZ,hImage]
  have hInnerImage : (F₀.filter (markedInnerResource A Z)).image emb=∅ := by
    rw [←markedResourceEmbedding_inner_filter f g A Z I J hA hZ,hImage,hInner]
  refine ⟨F₀,Finset.filter_subset _ _,hImage,?_,Finset.image_eq_empty.mp hInnerImage,?_,?_⟩
  · rw [Finset.image_sdiff _ _ emb.injective,hImage]
  · intro physical x
    have h := markedActiveVertexEmbedding_incidence_card_le tail head ktail khead tail' head' ktail' khead'
      ρ π f g hcomm e k ht hh hkt hkh H₀ Hₖ H₀' Hₖ' h₀ hₖ F₀ physical x
    rw [hImage] at h
    exact (show (_:ℝ)≤_ from Nat.cast_le.mpr h).trans (hInc physical (Sum.map f g x))
  · intro physical x
    have h := markedActiveVertexEmbedding_incidence_card_le tail head ktail khead tail' head' ktail' khead'
      ρ π f g hcomm e k ht hh hkt hkh H₀ Hₖ H₀' Hₖ' h₀ hₖ
      (F₀.filter (markedStarResource A Z)) physical x
    rw [hStarImage] at h
    exact (show (_:ℝ)≤_ from Nat.cast_le.mpr h).trans (hStar physical (Sum.map f g x))

end Oberwolfach
