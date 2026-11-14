module

public import Oberwolfach.FiniteFibreCodes
public import Oberwolfach.SubsetCounts
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

/-! Counting indexed c-sets containing prescribed vertices. The fibre
code preserves all indexed copies on the same vertex set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]

theorem uniform_resources_containing_count (R : C → Finset V) (c J : ℕ)
    (hR : ∀ C₀,(R C₀).card=c) (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (S : Finset V) (hS : S.card ≤ c) :
    Fintype.card {C₀ : C // S⊆R C₀} ≤ J*Fintype.card V^(c-S.card) := by
  obtain ⟨code,hcode⟩ := finite_fibre_codes R J hJ
  let B := {U : FixedSubset V c // S⊆U.val}
  let enc (C₀ : {C₀ : C // S⊆R C₀}) : B × Fin J :=
    (⟨⟨R C₀.val,hR C₀.val⟩,C₀.property⟩,code C₀.val)
  have hinj : Function.Injective enc := by
    intro D E he
    apply Subtype.ext
    apply hcode
    · exact congrArg (fun z : B × Fin J => z.1.val.val) he
    · exact congrArg Prod.snd he
  have hB : Fintype.card B ≤ Fintype.card V^(c-S.card) := by
    have he : Fintype.card B=(Fintype.card V-S.card).choose (c-S.card) := by
      convert fixedSubset_containing_card S hS using 1 <;> congr!
    rw [he]
    exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
  have hh := Fintype.card_le_of_injective enc hinj
  rw [Fintype.card_prod,Fintype.card_fin] at hh
  exact hh.trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_right J hB)

theorem uniform_resources_pair_count (R : C → Finset V) (c J : ℕ) (hc : 2 ≤ c)
    (hR : ∀ C₀,(R C₀).card=c) (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (u v : V) (huv : u≠v) :
    Fintype.card {C₀ : C // u∈R C₀ ∧ v∈R C₀} ≤ J*Fintype.card V^(c-2) := by
  have hcard : ({u,v}:Finset V).card=2 := by simp [huv]
  have hh := uniform_resources_containing_count R c J hR hJ {u,v} (by simpa only [hcard] using hc)
  simpa only [hcard,Finset.insert_subset_iff,Finset.singleton_subset_iff] using hh

end Oberwolfach
