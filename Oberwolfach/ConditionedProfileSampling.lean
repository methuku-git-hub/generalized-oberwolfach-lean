module

public import Oberwolfach.ConditionedProfileGeometry
public import Oberwolfach.ProfileInducedSampling
public import Oberwolfach.AbsorberProfileSampling

@[expose] public section

/-! Conditional concentration on the original class sample space.
The displayed probabilities include the root-inclusion probability.
No sum over possible root labels is introduced. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {V : Fin s → Type*} [∀ i,Fintype (V i)]
    {C : Type*} [Fintype C]

theorem profile_rooted_weighted_degree_tail
    (R : C → Finset (Σ i,V i)) (c J : ℕ) (hc : 2 ≤ c)
    (hR : ∀ C₀,(R C₀).card=c)
    (hJ : ∀ A : Finset (Σ i,V i),Fintype.card {C₀ : C // R C₀=A} ≤ J)
    (w : C → ℝ) (B : ℝ) (hB : 0 ≤ B) (hw : ∀ C₀,0 ≤ w C₀ ∧ w C₀ ≤ B)
    (T : ∀ i,Finset (V i)) (k : Fin s → ℕ)
    [∀ i,Nonempty (FixedSubset {v : V i // v∉T i} (k i))]
    [∀ i,Nonempty (FixedSubset (V i) ((T i).card+k i))]
    (hk : ∀ i,k i ≤ Fintype.card {v : V i // v∉T i})
    (v : Σ i,V i) (hv : v∈Finset.univ.sigma T) (t : ℝ) (ht : 0 ≤ t) :
    let μ := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) ((T i).card+k i)))
    let ν := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset {v : V i // v∉T i} (k i)))
    let f := fun τ => hypergraphWeightedDegree R (inducedResourceWeight R w (profileRootSet τ)) v
    let mean := ν.expectation (fun σ => f (fillProfileRoots T σ))
    μ.probability (fun τ => (∀ i,T i⊆(τ i).val) ∧ t ≤ |f τ-mean|) ≤
      μ.probability (fun τ => ∀ i,T i⊆(τ i).val)*
        (2*Real.exp (-2*t^2/((∑ i,(k i:ℝ))*
          (2*(J:ℝ)*((Finset.univ.sigma T).card+(∑ i,k i)+1:ℕ)^(c-2)*B)^2))) := by
  let ν := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset {v : V i // v∉T i} (k i)))
  let f := fun τ : ∀ i,FixedSubset (V i) ((T i).card+k i) =>
    hypergraphWeightedDegree R (inducedResourceWeight R w (profileRootSet τ)) v
  let mean := ν.expectation (fun σ => f (fillProfileRoots T σ))
  have htail := profile_induced_degree_tail (profileRootFreeEmbedding T) R c J hc hR hJ w B hB hw
    (Finset.univ.sigma T) v hv k hk t ht
  have he : (fun σ : ∀ i,FixedSubset {v : V i // v∉T i} (k i) =>
      hypergraphWeightedDegree R (inducedResourceWeight R w
        (Finset.univ.sigma T∪(profileRootSet σ).map (profileRootFreeEmbedding T))) v)=
      (fun σ => f (fillProfileRoots T σ)) := by
    funext σ
    rw [← fillProfileRoots_ground]
  change ν.probability (fun σ => t ≤ |_-ν.expectation _|) ≤ _ at htail
  have htail' : ν.probability (fun σ => t ≤ |f (fillProfileRoots T σ)-mean|) ≤ 2*Real.exp (-2*t^2/((∑ i,(k i:ℝ))*(2*(J:ℝ)*((Finset.univ.sigma T).card+(∑ i,k i)+1:ℕ)^(c-2)*B)^2)) := by
    have heEvent := congrArg
      (fun g : (∀ i,FixedSubset {v : V i // v∉T i} (k i)) → ℝ =>
        ν.probability (fun σ => t ≤ |g σ-ν.expectation g|)) he
    apply heEvent.symm.trans_le
    convert htail using 1 <;> congr!
  have hlaw := profile_root_conditional_probability T k (fun τ => t ≤ |f τ-mean|)
  change _ ≤ _
  rw [hlaw]
  exact mul_le_mul_of_nonneg_left htail' (finiteLaw_probability_nonneg _ _)

theorem absorberGroundCount_remove_fixed_roots {W Tpl : Type*} [Fintype W] [DecidableEq W]
    [DecidableEq C] [Fintype Tpl] [DecidableEq Tpl] {c : ℕ}
    (R : C → Finset W) (S : Tpl → VertexAbsorberTemplate c) (X Z A : Finset W) (hZX : Z⊆X) :
    absorberGroundCount R S X (Z∪A)=absorberGroundCount R S X A := by
  have hp (D : LabelledAbsorberFamily R S X) :
      labelledAbsorberFree R (S D.1) X D.2⊆Z∪A ↔ labelledAbsorberFree R (S D.1) X D.2⊆A := by
    constructor
    · intro h v hv
      have hnot : v∉Z := fun hz => Finset.disjoint_left.mp
        (labelled_absorber_factors R (S D.1) X D.2).1 hv (hZX hz)
      exact (Finset.mem_union.mp (h hv)).resolve_left hnot
    · exact fun h => h.trans Finset.subset_union_right
  unfold absorberGroundCount
  exact_mod_cast Fintype.card_congr (Equiv.subtypeEquivRight hp)

theorem profile_rooted_absorber_count_tail {W Tpl : Type*} [Fintype W] [DecidableEq W]
    [DecidableEq C] [Fintype Tpl] [DecidableEq Tpl] {c : ℕ}
    (e : (Σ i,V i) ↪ W) (R : C → Finset W) (S : Tpl → VertexAbsorberTemplate c) (X : Finset W)
    (J : ℕ) (hJ : ∀ A : Finset W,Fintype.card {C₀ : C // R C₀=A} ≤ J)
    (T : ∀ i,Finset (V i)) (k : Fin s → ℕ)
    [∀ i,Nonempty (FixedSubset {v : V i // v∉T i} (k i))]
    [∀ i,Nonempty (FixedSubset (V i) ((T i).card+k i))]
    (hk : ∀ i,k i ≤ Fintype.card {v : V i // v∉T i})
    (hTX : (Finset.univ.sigma T).map e⊆X) (t : ℝ) (ht : 0 ≤ t) :
    let μ := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) ((T i).card+k i)))
    let ν := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset {v : V i // v∉T i} (k i)))
    let f := fun τ => absorberGroundCount R S X ((profileRootSet τ).map e)
    let mean := ν.expectation (fun σ => f (fillProfileRoots T σ))
    μ.probability (fun τ => (∀ i,T i⊆(τ i).val) ∧ t ≤ |f τ-mean|) ≤
      μ.probability (fun τ => ∀ i,T i⊆(τ i).val)*
        (2*Real.exp (-2*t^2/((∑ i,(k i:ℝ))*
          (2*((c*c)*Fintype.card Tpl*X.card^c*J^(2*c+1):ℕ)*((∑ i,k i)+1:ℕ)^(c*c-1))^2))) := by
  let ν := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset {v : V i // v∉T i} (k i)))
  let f := fun τ : ∀ i,FixedSubset (V i) ((T i).card+k i) => absorberGroundCount R S X ((profileRootSet τ).map e)
  let mean := ν.expectation (fun σ => f (fillProfileRoots T σ))
  have htail := absorber_profile_count_tail ((profileRootFreeEmbedding T).trans e) R S X J hJ k hk t ht
  have he : (fun σ : ∀ i,FixedSubset {v : V i // v∉T i} (k i) =>
      absorberGroundCount R S X ((profileRootSet σ).map ((profileRootFreeEmbedding T).trans e)))=
      (fun σ => f (fillProfileRoots T σ)) := by
    funext σ
    dsimp [f]
    rw [fillProfileRoots_ground,Finset.map_union,Finset.map_map]
    exact (absorberGroundCount_remove_fixed_roots R S X ((Finset.univ.sigma T).map e) _ hTX).symm
  change ν.probability (fun σ => t ≤ |_-ν.expectation _|) ≤ _ at htail
  have htail' : ν.probability (fun σ => t ≤ |f (fillProfileRoots T σ)-mean|) ≤ 2*Real.exp (-2*t^2/((∑ i,(k i:ℝ))*(2*((c*c)*Fintype.card Tpl*X.card^c*J^(2*c+1):ℕ)*((∑ i,k i)+1:ℕ)^(c*c-1))^2)) := by
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
