module

public import Oberwolfach.AbsorberDeletionExpectation
public import Oberwolfach.LabelledRecordDeletionCounts

@[expose] public section

/-! Lower bounds for the actual sampled absorber count. The deleted
records are subtracted before multiplying by their inclusion probability. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sampling_probability_scaled_lower (p k t δ : ℝ) (h : ℕ)
    (ht : 0 < t) (hp : |(k/t)^h*p-1| ≤ δ) :
    (1-δ)*t^h ≤ p*k^h := by
  have hh : 1-δ ≤ (k/t)^h*p := by
    have hl := (abs_le.mp hp).1
    linarith
  have he : (k/t)^h*p*t^h=p*k^h := by
    rw [div_pow]
    field_simp
  calc
    _ ≤ (k/t)^h*p*t^h := mul_le_mul_of_nonneg_right hh (pow_nonneg ht.le _)
    _ = _ := he

theorem labelled_absorber_avoiding_lower {W C T : Type*}
    [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]
    [Fintype T] [DecidableEq T] {c : ℕ}
    (R : C → Finset W) (S : T → VertexAbsorberTemplate c) (X Z : Finset W) (J : ℕ)
    (hJ : ∀ A : Finset W,Fintype.card {C₀ : C // R C₀=A} ≤ J)
    (A L : ℝ) (hA : A ≤ Fintype.card (LabelledAbsorberFamily R S X))
    (hL : (Z.card*((c*c)*Fintype.card T*X.card^c*Fintype.card W^(c*c-1)*J^(2*c+1)):ℕ) ≤ L) :
    A-L ≤ (Fintype.card {D : LabelledAbsorberFamily R S X //
      Disjoint (labelledAbsorberFree R (S D.1) X D.2) Z}:ℝ) := by
  let P (D : LabelledAbsorberFamily R S X) := Disjoint (labelledAbsorberFree R (S D.1) X D.2) Z
  have hbad := labelled_absorber_free_deletion_count R S X Z J hJ
  have hpart : Fintype.card {D // P D}+Fintype.card {D // ¬P D}=
      Fintype.card (LabelledAbsorberFamily R S X) := by
    rw [Fintype.card_subtype_compl]
    exact Nat.add_sub_of_le (Fintype.card_subtype_le P)
  have hpart' : (Fintype.card {D // P D}:ℝ)+Fintype.card {D // ¬P D}=
      Fintype.card (LabelledAbsorberFamily R S X) := by exact_mod_cast hpart
  have hbad₀ : (Fintype.card {D // ¬P D}:ℝ) ≤
      (Z.card*((c*c)*Fintype.card T*X.card^c*Fintype.card W^(c*c-1)*J^(2*c+1)):ℕ) := by exact_mod_cast hbad
  have hbad' : (Fintype.card {D // ¬P D}:ℝ) ≤ L := hbad₀.trans hL
  change A-L ≤ (Fintype.card {D // P D}:ℝ)
  linarith

theorem absorber_deletion_profile_mean_lower
    {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
    {C T : Type*} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T] {c : ℕ}
    (R : C → Finset (Σ i,V i)) (S : T → VertexAbsorberTemplate c) (a : I → ℕ)
    (hR : ∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i)
    (X Z : Finset (Σ i,V i)) (J : ℕ)
    (hJ : ∀ A : Finset (Σ i,V i),Fintype.card {C₀ : C // R C₀=A} ≤ J)
    (m : I → ℕ) [∀ i,Nonempty (FixedSubset (ProfileRemainingClass Z i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (ProfileRemainingClass Z i))
    (α k t : ℝ) (hα : 0 ≤ α) (ht : 0 < t)
    (hcount : α*k^(c*c) ≤ Fintype.card (LabelledAbsorberFamily R S X))
    (hloss : (Z.card*((c*c)*Fintype.card T*X.card^c*Fintype.card (Σ i,V i)^(c*c-1)*J^(2*c+1)):ℕ) ≤
      α/4*k^(c*c))
    (hratio : |(k/t)^(c*c)*(∏ i,((m i).choose (c*a i):ℝ)/
      (Fintype.card (ProfileRemainingClass Z i)).choose (c*a i))-1| ≤ 1/4) :
    (α/2)*t^(c*c) ≤
      (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (ProfileRemainingClass Z i) (m i)))).expectation
        (fun σ => absorberGroundCount R S X ((profileRootSet σ).map (profileComplementEmbedding Z))) := by
  let p := ∏ i,((m i).choose (c*a i):ℝ)/(Fintype.card (ProfileRemainingClass Z i)).choose (c*a i)
  have hp : 0 ≤ p := Finset.prod_nonneg (fun i _ => by positivity)
  have hgood := labelled_absorber_avoiding_lower R S X Z J hJ (α*k^(c*c)) (α/4*k^(c*c)) hcount hloss
  have hgood' : (3/4)*α*k^(c*c) ≤ (Fintype.card {D : LabelledAbsorberFamily R S X //
      Disjoint (labelledAbsorberFree R (S D.1) X D.2) Z}:ℝ) := by linarith
  have hprob := sampling_probability_scaled_lower p k t (1/4) (c*c) ht hratio
  rw [absorber_deletion_profile_expectation R S a hR X Z m hm]
  change _ ≤ p*_
  calc
    _ ≤ (3/4)*α*((1-1/4)*t^(c*c)) := by nlinarith [pow_nonneg ht.le (c*c)]
    _ ≤ (3/4)*α*(p*k^(c*c)) := mul_le_mul_of_nonneg_left hprob (by positivity)
    _ = p*((3/4)*α*k^(c*c)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hgood' hp

end Oberwolfach
