module

public import Oberwolfach.ProfileDemandBounds
public import Oberwolfach.HypergraphWeightMoments

@[expose] public section

/-! The common class mean of the vertex-load defects follows from the
actual class profile of every cycle. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I C : Type*} [Fintype I] [Fintype C] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

theorem profile_weighted_degree_sum (R : C → Finset (Σ i,V i)) (w : C → ℝ) (a : I → ℕ)
    (hR : ∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i) (i : I) :
    (∑ v : V i,hypergraphWeightedDegree R w ⟨i,v⟩)=(a i:ℝ)*(∑ C₀,w C₀) := by
  unfold hypergraphWeightedDegree
  rw [Finset.sum_comm]
  have he (C₀ : C) : (∑ v : V i,if (⟨i,v⟩ : Σ i,V i)∈R C₀ then w C₀ else 0)=(a i:ℝ)*w C₀ := by
    rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,hR]
  simp_rw [he]
  exact (Finset.mul_sum _ _ _).symm

theorem profile_defect_class_sum (R : C → Finset (Σ i,V i)) (w : C → ℝ) (a : I → ℕ)
    (hR : ∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i)
    (k : ℝ) (hk : 0 < k) (hn : ∀ i,(Fintype.card (V i):ℝ)=(a i:ℝ)*k) (i : I) :
    (∑ v : V i,(1-hypergraphWeightedDegree R w ⟨i,v⟩))=
      (Fintype.card (V i):ℝ)*(1-(∑ C₀,w C₀)/k) := by
  rw [Finset.sum_sub_distrib,profile_weighted_degree_sum R w a hR i]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  rw [hn i]
  field_simp
  <;> ring

theorem profile_defect_centred_data [Nonempty I]
    (R : C → Finset (Σ i,V i)) (w : C → ℝ) (a : I → ℕ)
    (hR : ∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i)
    (k η : ℝ) (hk : 0 < k) (ha : ∀ i,1 ≤ a i)
    (hn : ∀ i,(Fintype.card (V i):ℝ)=(a i:ℝ)*k)
    (herr : ∀ i v,|1-hypergraphWeightedDegree R w ⟨i,v⟩| ≤ η) :
    let m := 1-(∑ C₀,w C₀)/k
    let y := fun i (v : V i) => 1-hypergraphWeightedDegree R w ⟨i,v⟩-m
    |m| ≤ η ∧ (∀ i,∑ v,y i v=0) ∧ (∀ i v,|y i v| ≤ 2*η) := by
  dsimp only
  let m := 1-(∑ C₀,w C₀)/k
  have hsum := profile_defect_class_sum R w a hR k hk hn
  have hmean : |m| ≤ η := by
    obtain ⟨i⟩ := ‹Nonempty I›
    have hn0 : (0:ℝ)<Fintype.card (V i) := by
      rw [hn i]
      have hai : (0:ℝ)<a i := by exact_mod_cast (show 0<a i by have hh:=ha i;omega)
      positivity
    have hh : |(Fintype.card (V i):ℝ)*m| ≤ (Fintype.card (V i):ℝ)*η := by
      rw [← hsum i]
      calc
        _ ≤ ∑ v : V i,|1-hypergraphWeightedDegree R w ⟨i,v⟩| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _v : V i,η := Finset.sum_le_sum (fun v _ => herr i v)
        _ = _ := by simp
    rw [abs_mul,abs_of_nonneg hn0.le] at hh
    exact (mul_le_mul_iff_right₀ hn0).mp hh
  refine ⟨hmean,?_,?_⟩
  · intro i
    rw [Finset.sum_sub_distrib,hsum i]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    ring
  · intro i v
    calc
      _ ≤ |1-hypergraphWeightedDegree R w ⟨i,v⟩|+|m| := by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (1-hypergraphWeightedDegree R w ⟨i,v⟩) 0 m
      _ ≤ η+η := add_le_add (herr i v) hmean
      _ = _ := by ring

end Oberwolfach
