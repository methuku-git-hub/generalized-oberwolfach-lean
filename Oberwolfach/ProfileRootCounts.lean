module

public import Oberwolfach.ProfileRootSampling
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

/-! Admissible roots are exactly the sets with the prescribed class
profile. Their total number is bounded before choosing the reservoir. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

theorem profileRootSet_injective (a : I → ℕ) :
    Function.Injective (profileRootSet (V:=V) (a:=a)) := by
  intro σ τ he
  funext i
  apply Subtype.ext
  ext v
  have hh : (⟨i,v⟩ : Σ i,V i)∈profileRootSet σ ↔ (⟨i,v⟩ : Σ i,V i)∈profileRootSet τ := by rw [he]
  simpa only [profileRootSet_mem] using hh

theorem profile_root_family_card (a : I → ℕ) (c : ℕ) (ha : ∑ i,a i=c) :
    Fintype.card (∀ i,FixedSubset (V i) (a i)) ≤ Fintype.card (Σ i,V i)^c := by
  let f (σ : ∀ i,FixedSubset (V i) (a i)) : FixedSubset (Σ i,V i) c :=
    ⟨profileRootSet σ,(profileRootSet_card σ).trans ha⟩
  have hf : Function.Injective f := by
    intro σ τ he
    exact profileRootSet_injective a (congrArg Subtype.val he)
  have hh := Fintype.card_le_of_injective f hf
  have hcard : Fintype.card (FixedSubset (Σ i,V i) c)=(Fintype.card (Σ i,V i)).choose c := by
    exact Fintype.card_finset_len c
  rw [hcard] at hh
  exact hh.trans (Nat.choose_le_pow _ _)

theorem profileRootSet_class_card {a : I → ℕ} (σ : ∀ i,FixedSubset (V i) (a i)) (i : I) :
    (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈profileRootSet σ)).card=a i := by
  have he : Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈profileRootSet σ)=(σ i).val := by
    ext v;simp only [Finset.mem_filter,Finset.mem_univ,true_and,profileRootSet_mem]
  rw [he,(σ i).property]

theorem exists_profile_root_of_class_sizes (a : I → ℕ) (X : Finset (Σ i,V i))
    (hX : ∀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈X)).card=a i) :
    ∃ σ : ∀ i,FixedSubset (V i) (a i),profileRootSet σ=X := by
  refine ⟨fun i => ⟨Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈X),hX i⟩,?_⟩
  ext v
  rcases v with ⟨i,v⟩
  simp [profileRootSet]

end Oberwolfach
