module

public import Oberwolfach.UniformResourceCounts

@[expose] public section

/-! Count actual indexed resources in a prescribed finite ground set.
This is a local-order count, not an ambient-order estimate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]

theorem uniform_resources_between_count (R : C → Finset V) (c J : ℕ)
    (hR : ∀ C₀,(R C₀).card=c) (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (S Y : Finset V) (hSY : S⊆Y) (hS : S.card ≤ c) :
    Fintype.card {C₀ : C // S⊆R C₀ ∧ R C₀⊆Y} ≤ J*Y.card^(c-S.card) := by
  obtain ⟨code,hcode⟩ := finite_fibre_codes R J hJ
  let B := {U : Finset V // U∈(Y.powersetCard c).filter (S⊆·)}
  let enc (D : {C₀ : C // S⊆R C₀ ∧ R C₀⊆Y}) : B×Fin J :=
    (⟨R D.val,Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨D.property.2,hR D.val⟩,D.property.1⟩⟩,
      code D.val)
  have hi : Function.Injective enc := by
    intro D E he
    apply Subtype.ext
    exact hcode D.val E.val (congrArg (fun z : B×Fin J => z.1.val) he) (congrArg Prod.snd he)
  have hb : Fintype.card B ≤ Y.card^(c-S.card) := by
    rw [Fintype.card_coe,Finset.card_filter_powersetCard_subset S Y c hSY hS]
    exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
  have hh := Fintype.card_le_of_injective enc hi
  rw [Fintype.card_prod,Fintype.card_fin] at hh
  exact hh.trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_right J hb)

theorem uniform_resources_local_pair_count (R : C → Finset V) (c J : ℕ) (hc : 2 ≤ c)
    (hR : ∀ C₀,(R C₀).card=c) (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (Y : Finset V) (u v : V) (hu : u∈Y) (hv : v∈Y) (huv : u≠v) :
    Fintype.card {C₀ : C // u∈R C₀ ∧ v∈R C₀ ∧ R C₀⊆Y} ≤ J*Y.card^(c-2) := by
  have hcard : ({u,v}:Finset V).card=2 := by simp [huv]
  have hh := uniform_resources_between_count R c J hR hJ {u,v} Y
    (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hu
      · have he := Finset.mem_singleton.mp hx
        subst x
        exact hv) (by simpa only [hcard] using hc)
  simpa only [hcard,Finset.insert_subset_iff,Finset.singleton_subset_iff,and_assoc] using hh

end Oberwolfach
