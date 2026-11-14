module

public import Oberwolfach.NestedProfileConditioning
public import Oberwolfach.RootedInducedWeightIdentity
public import Oberwolfach.FixedSizeProfileConditioning

@[expose] public section

/-! Exact conditional means for the original weighted cycles. The
conditioned sample contributes at most the one explicitly retained root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
    {C : Type*} [Fintype C]

theorem insert_union_of_singleton_subset {W : Type*} [DecidableEq W]
    (v : W) (A B : Finset W) (hA : A⊆{v}) : insert v (A∪B)=insert v B := by
  ext x
  simp only [Finset.mem_insert,Finset.mem_union]
  constructor
  · rintro (rfl|hx|hx)
    · exact Or.inl rfl
    · exact Or.inl (Finset.mem_singleton.mp (hA hx))
    · exact Or.inr hx
  · rintro (rfl|hx)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr hx)

theorem conditional_root_original_mean
    (R : C → Finset (Σ i,V i)) (w : C → ℝ) (a : I → ℕ)
    (hR : ∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i)
    (F : Finset (Σ i,V i)) (T : ∀ i,Finset (ProfileRemainingClass F i))
    (m : I → ℕ) (hT : ∀ i,(T i).card ≤ m i)
    [∀ i,Nonempty (FixedSubset {v : ProfileRemainingClass F i // v∉T i} (m i-(T i).card))]
    (hm : ∀ i,m i-(T i).card ≤ Fintype.card {v : ProfileRemainingClass F i // v∉T i})
    (v : Σ i,V i) (hroot : (Finset.univ.sigma T).map (profileComplementEmbedding F)⊆{v}) :
    let ν := FiniteLaw.pi (fun i => FiniteLaw.uniform
      (FixedSubset {v : ProfileRemainingClass F i // v∉T i} (m i-(T i).card)))
    ν.expectation (fun σ => hypergraphWeightedDegree R (inducedResourceWeight R w
      (insert v ((profileRootSet (fillProfileRootsAtSize T m hT σ)).map (profileComplementEmbedding F)))) v)=
      (∏ i,((m i-(T i).card).choose (a i-(if v.1=i then 1 else 0)):ℝ)/
        (Fintype.card {v : ProfileRemainingClass F i // v∉T i}).choose (a i-(if v.1=i then 1 else 0)))*
        hypergraphWeightedDegree R
          (vertexRestrictedWeight R w ((F∪(Finset.univ.sigma T).map (profileComplementEmbedding F)).erase v)) v := by
  let e := (profileRootFreeEmbedding T).trans (profileComplementEmbedding F)
  have heground (σ : ∀ i,FixedSubset {v : ProfileRemainingClass F i // v∉T i} (m i-(T i).card)) :
      insert v ((profileRootSet (fillProfileRootsAtSize T m hT σ)).map (profileComplementEmbedding F))=
        insert v ((profileRootSet σ).map e) := by
    rw [fillProfileRootsAtSize_ground,Finset.map_union,Finset.map_map]
    exact insert_union_of_singleton_subset v _ _ hroot
  dsimp only
  simp_rw [heground]
  exact embedded_rooted_original_weight_expectation e (nested_profile_embedding_class F T) R w a hR
    (F∪(Finset.univ.sigma T).map (profileComplementEmbedding F)) (nested_profile_embedding_range F T)
    v (fun i => m i-(T i).card) hm

end Oberwolfach
