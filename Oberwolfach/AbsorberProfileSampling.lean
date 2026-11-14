module

public import Oberwolfach.LabelledLocalCounts
public import Oberwolfach.FiniteSupportCounts
public import Oberwolfach.ProfileSubsetExchange
public import Oberwolfach.UniformProfileConcentration

@[expose] public section

/-! Concentration of actual labelled absorber counts under classwise
sampling, with all original templates and cycle identifiers retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 4200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {V : Fin s → Type*} [∀ i,Fintype (V i)]
    {W C T : Type*} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]
    [Fintype T] [DecidableEq T] {c : ℕ}

def absorberGroundCount (R : C → Finset W) (S : T → VertexAbsorberTemplate c) (X A : Finset W) : ℝ :=
  Fintype.card {D : LabelledAbsorberFamily R S X // labelledAbsorberFree R (S D.1) X D.2⊆A}

theorem absorber_profile_count_exchange (e : (Σ i,V i) ↪ W)
    (R : C → Finset W) (S : T → VertexAbsorberTemplate c) (X : Finset W)
    (J : ℕ) (hJ : ∀ A : Finset W,Fintype.card {C₀ : C // R C₀=A} ≤ J)
    {m : Fin s → ℕ} (σ τ : ∀ i,FixedSubset (V i) (m i)) (i : Fin s)
    (hagree : ∀ j,j≠i → σ j=τ j) (x y : V i)
    (he : τ i=fixedSubsetMap (Equiv.swap x y) (σ i)) :
    |absorberGroundCount R S X ((profileRootSet σ).map e)-
      absorberGroundCount R S X ((profileRootSet τ).map e)| ≤
      2*((c*c)*Fintype.card T*X.card^c*J^(2*c+1):ℕ)*((∑ j,m j)+1:ℕ)^(c*c-1) := by
  let A := (profileRootSet σ).map e
  let B := (profileRootSet τ).map e
  let D := (c*c)*Fintype.card T*X.card^c*J^(2*c+1)
  let K := D*((∑ j,m j)+1)^(c*c-1)
  have hb := profileSample_exchange_card_bounds e (∅ : Finset W) σ τ i hagree x y he
  simp only [Finset.empty_union,Finset.card_empty,zero_add] at hb
  have hK (v : W) : Fintype.card {d : LabelledAbsorberFamily R S X //
      labelledAbsorberFree R (S d.1) X d.2⊆A∪B ∧ v∈labelledAbsorberFree R (S d.1) X d.2} ≤ K := by
    calc
      _ ≤ (c*c)*Fintype.card T*X.card^c*(A∪B).card^(c*c-1)*J^(2*c+1) :=
        labelled_absorber_local_free_vertex_count R S X (A∪B) J hJ v
      _ = D*(A∪B).card^(c*c-1) := by dsimp [D];ring
      _ ≤ K := Nat.mul_le_mul_left D (Nat.pow_le_pow_left hb.2.2 _)
  have hh := finite_support_count_difference
    (fun d : LabelledAbsorberFamily R S X => labelledAbsorberFree R (S d.1) X d.2) A B K hK
  have hsum : (A\B).card+(B\A).card ≤ 2 := by dsimp [A,B];omega
  have hsumR : (((A\B).card+(B\A).card:ℕ):ℝ) ≤ 2 := by exact_mod_cast hsum
  have hh' := hh.trans (mul_le_mul_of_nonneg_right hsumR (Nat.cast_nonneg K))
  simpa only [K,Nat.cast_mul,mul_assoc,absorberGroundCount,D,A,B,Nat.cast_pow] using hh'

theorem absorber_profile_count_tail (e : (Σ i,V i) ↪ W)
    (R : C → Finset W) (S : T → VertexAbsorberTemplate c) (X : Finset W)
    (J : ℕ) (hJ : ∀ A : Finset W,Fintype.card {C₀ : C // R C₀=A} ≤ J)
    (m : Fin s → ℕ) [∀ i,Nonempty (FixedSubset (V i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (V i)) (t : ℝ) (ht : 0 ≤ t) :
    let μ := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))
    let f := fun σ => absorberGroundCount R S X ((profileRootSet σ).map e)
    μ.probability (fun σ => t ≤ |f σ-μ.expectation f|) ≤
      2*Real.exp (-2*t^2/((∑ i,(m i:ℝ))*
        (2*((c*c)*Fintype.card T*X.card^c*J^(2*c+1):ℕ)*((∑ j,m j)+1:ℕ)^(c*c-1))^2)) := by
  apply uniform_profile_absolute_tail m hm _ _ (by positivity) _ t ht
  intro i σ τ ha x y he
  exact absorber_profile_count_exchange e R S X J hJ σ τ i ha x y he

end Oberwolfach
