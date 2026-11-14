module

public import Oberwolfach.FixedCoordinateCounts

@[expose] public section

/-! Prescribing distinct vertices fixes their classes. If two prescriptions
conflict in one class, no selection satisfies them. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem prescribedVertices_card_le {I X V : Type*}
    [Fintype I] [Fintype X] [DecidableEq I] [DecidableEq V]
    (S : Finset V) (cl : V → I) (val : V → X)
    (hinj : Function.Injective (fun v => (cl v, val v))) :
    Fintype.card {f : I → X // ∀ v ∈ S, f (cl v) = val v} ≤
      Fintype.card X ^ (Fintype.card I - S.card) := by
  classical
  by_cases hex : ∃ f : I → X, ∀ v ∈ S, f (cl v) = val v
  · obtain ⟨f₀, hf₀⟩ := hex
    have hcl : Set.InjOn cl S := by
      intro u hu v hv huv
      apply hinj
      apply Prod.ext huv
      change val u = val v
      rw [← hf₀ u hu, ← hf₀ v hv, huv]
    have hcard : (S.image cl).card = S.card := Finset.card_image_of_injOn hcl
    have hp (f : I → X) : (∀ v ∈ S, f (cl v) = val v) ↔
        (∀ i ∈ S.image cl, f i = f₀ i) := by
      constructor
      · intro h i hi
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
        exact (h v hv).trans (hf₀ v hv).symm
      · intro h v hv
        exact (h (cl v) (Finset.mem_image.mpr ⟨v, hv, rfl⟩)).trans (hf₀ v hv)
    have he := Fintype.card_congr (Equiv.subtypeEquivRight hp)
    rw [he, fixedCoordinates_card, hcard]
  · have hz : IsEmpty {f : I → X // ∀ v ∈ S, f (cl v) = val v} :=
      ⟨fun f => hex ⟨f.val, f.property⟩⟩
    letI := hz
    simp only [Fintype.card_eq_zero, zero_le]

theorem prescribedVertices_weight_le {I X V : Type*}
    [Fintype I] [Fintype X] [DecidableEq I] [DecidableEq V]
    (S : Finset V) (cl : V → I) (val : V → X)
    (hinj : Function.Injective (fun v => (cl v, val v)))
    (w : (I → X) → ℝ) (M : ℝ) (hM : 0 ≤ M) (hw : ∀ f, w f ≤ M) :
    (∑ f : I → X, if (∀ v ∈ S, f (cl v) = val v) then w f else 0) ≤
      (Fintype.card X : ℝ) ^ (Fintype.card I - S.card) * M := by
  classical
  calc
    _ ≤ ∑ f : I → X, if (∀ v ∈ S, f (cl v) = val v) then M else 0 := by
      apply Finset.sum_le_sum
      intro f _
      split_ifs
      · exact hw f
      · exact le_refl _
    _ = (Fintype.card {f : I → X // ∀ v ∈ S, f (cl v) = val v} : ℝ) * M := by
      simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
        Fintype.card_subtype]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by
      exact_mod_cast prescribedVertices_card_le S cl val hinj) hM

end Oberwolfach
