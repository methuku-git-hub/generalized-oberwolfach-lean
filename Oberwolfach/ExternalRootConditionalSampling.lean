module

public import Oberwolfach.ConditionedProfileSampling

@[expose] public section

/-! Root-conditioned concentration with an explicit ambient embedding
and a fixed set of retained external vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 256
set_option maxHeartbeats 3200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {V : Fin s → Type*} [∀ i,Fintype (V i)]
    {W C : Type*} [Fintype W] [DecidableEq W] [Fintype C]

theorem profile_external_root_conditioned_degree_tail
    (e : (Σ i,V i) ↪ W) (R : C → Finset W) (c J : ℕ) (hc : 2 ≤ c)
    (hR : ∀ C₀,(R C₀).card=c)
    (hJ : ∀ Y : Finset W,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (w : C → ℝ) (B : ℝ) (hB : 0 ≤ B) (hw : ∀ C₀,0 ≤ w C₀ ∧ w C₀ ≤ B)
    (A : Finset W) (T : ∀ i,Finset (V i)) (k : Fin s → ℕ)
    [∀ i,Nonempty (FixedSubset {v : V i // v∉T i} (k i))]
    [∀ i,Nonempty (FixedSubset (V i) ((T i).card+k i))]
    (hk : ∀ i,k i ≤ Fintype.card {v : V i // v∉T i})
    (v : W) (hv : v∈A∪(Finset.univ.sigma T).map e) (t : ℝ) (ht : 0 ≤ t) :
    let μ := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) ((T i).card+k i)))
    let ν := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset {v : V i // v∉T i} (k i)))
    let f := fun τ => hypergraphWeightedDegree R (inducedResourceWeight R w (A∪(profileRootSet τ).map e)) v
    let mean := ν.expectation (fun σ => f (fillProfileRoots T σ))
    μ.probability (fun τ => (∀ i,T i⊆(τ i).val) ∧ t ≤ |f τ-mean|) ≤
      μ.probability (fun τ => ∀ i,T i⊆(τ i).val)*
        (2*Real.exp (-2*t^2/((∑ i,(k i:ℝ))*
          (2*(J:ℝ)*((A∪(Finset.univ.sigma T).map e).card+(∑ i,k i)+1:ℕ)^(c-2)*B)^2))) := by
  let ν := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset {v : V i // v∉T i} (k i)))
  let f := fun τ : ∀ i,FixedSubset (V i) ((T i).card+k i) =>
    hypergraphWeightedDegree R (inducedResourceWeight R w (A∪(profileRootSet τ).map e)) v
  let mean := ν.expectation (fun σ => f (fillProfileRoots T σ))
  have htail := profile_induced_degree_tail ((profileRootFreeEmbedding T).trans e) R c J hc hR hJ w B hB hw
    (A∪(Finset.univ.sigma T).map e) v hv k hk t ht
  have he : (fun σ : ∀ i,FixedSubset {v : V i // v∉T i} (k i) =>
      hypergraphWeightedDegree R (inducedResourceWeight R w
        ((A∪(Finset.univ.sigma T).map e)∪(profileRootSet σ).map ((profileRootFreeEmbedding T).trans e))) v)=
      (fun σ => f (fillProfileRoots T σ)) := by
    funext σ
    dsimp [f]
    rw [fillProfileRoots_ground,Finset.map_union,Finset.map_map,Finset.union_assoc]
  change ν.probability (fun σ => t ≤ |_-ν.expectation _|) ≤ _ at htail
  have htail' : ν.probability (fun σ => t ≤ |f (fillProfileRoots T σ)-mean|) ≤
      2*Real.exp (-2*t^2/((∑ i,(k i:ℝ))*(2*(J:ℝ)*((A∪(Finset.univ.sigma T).map e).card+(∑ i,k i)+1:ℕ)^(c-2)*B)^2)) := by
    have heEvent := congrArg
      (fun g : (∀ i,FixedSubset {v : V i // v∉T i} (k i)) → ℝ =>
        ν.probability (fun σ => t ≤ |g σ-ν.expectation g|)) he
    apply heEvent.symm.trans_le
    convert htail using 1 <;> congr!
  have hlaw := profile_root_conditional_probability T k (fun τ => t ≤ |f τ-mean|)
  change _ ≤ _
  rw [hlaw]
  exact mul_le_mul_of_nonneg_left htail' (finiteLaw_probability_nonneg _ _)

end Oberwolfach
