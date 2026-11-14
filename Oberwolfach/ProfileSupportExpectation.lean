module

public import Oberwolfach.EmbeddedProfileSampling
public import Oberwolfach.AbsorberFreeFactors
public import Oberwolfach.SigmaClassCounts

@[expose] public section

/-! Exact expected counts of a fixed indexed family with specified
free-label class sizes. This applies after restricting the family to
avoid the forbidden and conditioned root labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 3200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
    {W D : Type*} [DecidableEq W] [Fintype D]

theorem embedded_profile_support_count_expectation (e : (Σ i,V i) ↪ W)
    (F : D → Finset W) (a m : I → ℕ)
    (hF : ∀ d,F d⊆Finset.univ.map e)
    (ha : ∀ d i,(Finset.univ.filter (fun v : V i => e ⟨i,v⟩∈F d)).card=a i)
    [∀ i,Nonempty (FixedSubset (V i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (V i)) :
    (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))).expectation
      (fun σ => (Fintype.card {d : D // F d⊆(profileRootSet σ).map e}:ℝ))=
      (∏ i,((m i).choose (a i):ℝ)/(Fintype.card (V i)).choose (a i))*Fintype.card D := by
  simp only [Fintype.card_subtype]
  have hp (d : D) :
      (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))).probability
        (fun σ => F d⊆(profileRootSet σ).map e)=
      ∏ i,((m i).choose (a i):ℝ)/(Fintype.card (V i)).choose (a i) := by
    have hh := embedded_profile_inclusion_probability e ∅ (F d)
      (by simpa only [Finset.empty_union] using hF d) m hm
    simpa only [Finset.empty_union,Finset.notMem_empty,not_false_eq_true,and_true,ha] using hh
  calc
    _ = ∑ d : D,(FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))).probability
        (fun σ => F d⊆(profileRootSet σ).map e) := by
      convert finiteLaw_expectation_count
        (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))) Finset.univ
        (fun d σ => F d⊆(profileRootSet σ).map e) using 1 <;> congr!
    _ = _ := by simp only [hp,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm]

theorem labelled_absorber_free_class_card {C : Type*} [Fintype C] [DecidableEq C]
    {c : ℕ} (R : C → Finset (Σ i,V i)) (S : VertexAbsorberTemplate c) (X : Finset (Σ i,V i))
    (A : LabelledCycleRecord R S.val X) (a : I → ℕ)
    (hR : ∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i) (i : I) :
    (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈labelledAbsorberFree R S X A)).card=c*a i := by
  have hh := free_absorber_class_card R S (forgetAbsorberRoots R S X A) Sigma.fst a
    (fun C₀ j => (sigma_finset_class_card (R C₀) j).trans (hR C₀ j)) i
  have he : freeAbsorberVertices R S (forgetAbsorberRoots R S X A)=labelledAbsorberFree R S X A := by
    ext v
    simp only [freeAbsorberVertices,labelledAbsorberFree,Finset.mem_map,Finset.mem_image,
      Finset.mem_univ,true_and,forgetAbsorberRoots]
    rfl
  rw [he,sigma_finset_class_card] at hh
  exact hh

end Oberwolfach
