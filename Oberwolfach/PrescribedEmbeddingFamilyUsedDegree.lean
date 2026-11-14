module

public import Oberwolfach.PartialImageDegree
public import Oberwolfach.PrescribedEmbeddingUsedDegree

@[expose] public section
/-! Apply the used-edge degree bound to actual injective partial source images. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem prescribed_embedding_used_degree_from_partial_images
    (X:I→Type) [∀ i,Fintype (X i)] (Q:∀ i,SimpleGraph (X i))
    (φ:∀ i,X i↪V) (H:I→SimpleGraph V) (old fresh:I→V→Prop)
    (hsource:∀ i,H i≤(Q i).map (φ i))
    (hsourceDegree:∀ i x,(Q i).degree x≤2)
    (hocc:∀ i v,(∃ x,φ i x=v)→ old i v ∨ fresh i v)
    (G J K:SimpleGraph V)
    (hcover:∀ v,G.neighborFinset v⊆Finset.univ.biUnion (fun i=>(H i).neighborFinset v))
    (hforbid:∀ v,K.neighborFinset v⊆G.neighborFinset v∪J.neighborFinset v)
    (δ n t:ℝ)
    (hold:∀ v,((Finset.univ.filter (fun i=>old i v)).card:ℝ)≤δ*n)
    (hfresh:∀ v,((Finset.univ.filter (fun i=>fresh i v)).card:ℝ)≤t+1)
    (hJ:∀ v,(J.degree v:ℝ)≤δ*n):
    ∀ v,(G.degree v:ℝ)≤2*δ*n+2*t+2 ∧ (K.degree v:ℝ)≤3*δ*n+2*t+2 := by
  apply prescribed_embedding_used_degree_bound H old fresh ?_ G J K hcover hforbid δ n t hold hfresh hJ
  intro i v
  have hi:=partial_injective_image_degree (Q i) (φ i) (H i) (hsource i) (hsourceDegree i) v
  by_cases hv:∃ x,φ i x=v
  · have hor:=hocc i v hv
    simpa [hor,hv] using hi
  · by_cases hor:old i v ∨ fresh i v
    · simp only [if_pos hor]
      simp only [if_neg hv] at hi
      omega
    · simpa [hor,hv] using hi
end Oberwolfach
