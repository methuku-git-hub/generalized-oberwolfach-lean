module

public import Oberwolfach.ProfileDemandCoefficients
public import Oberwolfach.CommonEvents

@[expose] public section

/-! The concrete root vertex set under the prescribed class sampling
law, with its exact one-vertex marginal and intersection bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

def profileRootSet {a : I → ℕ} (σ : ∀ i,FixedSubset (V i) (a i)) : Finset (Σ i,V i) :=
  Finset.univ.filter (fun v => v.2∈(σ v.1).val)

theorem profileRootSet_mem {a : I → ℕ} (σ : ∀ i,FixedSubset (V i) (a i)) (i : I) (v : V i) :
    (⟨i,v⟩ : Σ i,V i)∈profileRootSet σ ↔ v∈(σ i).val := by simp [profileRootSet]

theorem sigma_finset_card (S : Finset (Σ i,V i)) :
    S.card=∑ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈S)).card := by
  let e : S ≃ Σ i,{v : V i // (⟨i,v⟩ : Σ i,V i)∈S} := {
    toFun v := ⟨v.val.1,⟨v.val.2,v.property⟩⟩
    invFun v := ⟨⟨v.1,v.2.val⟩,v.2.property⟩
    left_inv := by rintro ⟨⟨i,v⟩,h⟩;rfl
    right_inv := by rintro ⟨i,⟨v,h⟩⟩;rfl }
  have hh := Fintype.card_congr e
  simpa only [Fintype.card_coe,Fintype.card_sigma,Fintype.card_subtype,Finset.filter_mem_eq_inter,Finset.univ_inter] using hh

theorem profileRootSet_card {a : I → ℕ} (σ : ∀ i,FixedSubset (V i) (a i)) :
    (profileRootSet σ).card=∑ i,a i := by
  rw [sigma_finset_card]
  apply Finset.sum_congr rfl
  intro i _
  have he : Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈profileRootSet σ)=(σ i).val := by
    ext v;simp [profileRootSet]
  rw [he,(σ i).property]

theorem profileRootSet_vertex_probability (a : I → ℕ)
    [∀ i,Nonempty (FixedSubset (V i) (a i))]
    (k : ℝ) (hk : 1 < k) (ha : ∀ i,1 ≤ a i)
    (hn : ∀ i,(Fintype.card (V i):ℝ)=(a i:ℝ)*k) (v : Σ i,V i) :
    (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (a i)))).probability
      (fun σ => v∈profileRootSet σ)=1/k := by
  rcases v with ⟨i,v⟩
  let μ := fun j => FiniteLaw.uniform (FixedSubset (V j) (a j))
  let : ∀ j,MeasurableSpace (FixedSubset (V j) (a j)) := fun _ => ⊤
  let : ∀ j,MeasurableSingletonClass (FixedSubset (V j) (a j)) := fun _ => ⟨fun _ => trivial⟩
  have hai : (0:ℝ)<a i := by exact_mod_cast (show 0<a i by have hh:=ha i;omega)
  have hr : a i ≤ Fintype.card (V i) := by
    have hh : (a i:ℝ) ≤ Fintype.card (V i) := by rw [hn i];nlinarith
    exact_mod_cast hh
  have hh := finiteLaw_coordinate_expectation μ i (fun S => if v∈S.val then (1:ℝ) else 0)
  have hm := fixedSubset_vertex_probability (V:=V i) hr v
  have he : (FiniteLaw.pi μ).probability (fun σ => v∈(σ i).val)=(μ i).probability (fun S => v∈S.val) := by
    simp only [FiniteLaw.expectation,FiniteLaw.probability,mul_ite,mul_one,mul_zero] at hh ⊢
    convert hh using 1 <;> congr!
  simp only [profileRootSet_mem]
  rw [he,hm,hn i]
  field_simp


theorem profileRootSet_hit_probability (a : I → ℕ)
    [∀ i,Nonempty (FixedSubset (V i) (a i))]
    (k : ℝ) (hk : 1 < k) (ha : ∀ i,1 ≤ a i)
    (hn : ∀ i,(Fintype.card (V i):ℝ)=(a i:ℝ)*k) (S : Finset (Σ i,V i)) :
    (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (a i)))).probability
      (fun σ => (S∩profileRootSet σ).Nonempty) ≤ S.card/k := by
  let μ := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (a i)))
  have he : (fun σ : ∀ i,FixedSubset (V i) (a i) => (S∩profileRootSet σ).Nonempty)=
      (fun σ => ∃ v∈S,v∈profileRootSet σ) := by
    funext σ;apply propext;simp [Finset.Nonempty]
  rw [he]
  have hh := finiteLaw_union_bound μ S (fun v σ => v∈profileRootSet σ)
  dsimp [μ] at hh
  simp_rw [profileRootSet_vertex_probability a k hk ha hn] at hh
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_one_div] using hh

end Oberwolfach
