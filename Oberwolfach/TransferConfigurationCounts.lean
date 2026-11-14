module

public import Oberwolfach.TransferConfigurationBounds

@[expose] public section

/-! The number of transfer configurations containing a specified set of free
labels is bounded by the corresponding number of functions on r squared positions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem OrdinaryTransferConfiguration.labels_injective {V U : Type*} {r : ℕ} {hr : 3≤r}
    {Q F : SimpleGraph V} {H : V → U → Prop} {v : V} {u u' : U} :
    Function.Injective (fun T : OrdinaryTransferConfiguration hr Q F H v u u' =>
      (T.labels : Fin r × Fin r → V)) := by
  intro T T' h
  have he : T.labels=T'.labels := Function.Embedding.ext (congrFun h)
  cases T
  cases T'
  cases he
  rfl

theorem ordinary_transfer_configuration_root_count {V U : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} {hr : 3≤r} {Q F : SimpleGraph V} {H : V → U → Prop}
    {v : V} {u u' : U} (S : Finset V) :
    (∑ T : OrdinaryTransferConfiguration hr Q F H v u u',
      if (↑S:Set V)⊆Set.range T.labels then (1:ℝ) else 0)≤
      ((r:ℝ)^2)^S.card*(Fintype.card V:ℝ)^(r^2-S.card) := by
  let g (f : Fin r × Fin r → V) := if (∀ z∈S,z∈Set.range f) then (1:ℝ) else 0
  have hg (f : Fin r × Fin r → V) : 0≤g f := by dsimp [g];split_ifs <;> norm_num
  calc
    _ = ∑ T : OrdinaryTransferConfiguration hr Q F H v u u',g T.labels := by
      apply Finset.sum_congr rfl
      intro T _
      dsimp only [g]
      simp only [Set.subset_def,Finset.mem_coe]
    _ ≤ ∑ f : Fin r × Fin r → V,g f :=
      finite_injective_sum_le _ OrdinaryTransferConfiguration.labels_injective g hg
    _ ≤ _ := by
      have hh := functions_cover_roots_count ((⟨0,by omega⟩,⟨0,by omega⟩):Fin r × Fin r) S
      simpa only [Fintype.card_prod,Fintype.card_fin,← pow_two,Nat.cast_pow] using hh

theorem OrdinaryTransferConfiguration.erased_rim_subset {V U : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} {hr : 3≤r} {Q F : SimpleGraph V} {H : V → U → Prop} {v : V} {u u' : U}
    (T : OrdinaryTransferConfiguration hr Q F H v u u') (D : OrdinaryWheel Q F H r)
    (hD : T.weight D≠0) :
    (↑((ordinaryWheelRim D).support.toFinset.erase v):Set V)⊆Set.range T.labels := by
  intro z hz
  have he := Finset.mem_erase.mp hz
  have hs := (T.weight_support D hD).2 (Set.mem_toFinset.mp he.2)
  exact (Set.mem_insert_iff.mp hs).resolve_left he.1

theorem ordinary_transfer_coefficient_sum_bound {V U : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} {hr : 3≤r} {Q F : SimpleGraph V} {H : V → U → Prop}
    {v : V} {u u' : U} (D : OrdinaryWheel Q F H r) :
    (∑ T : OrdinaryTransferConfiguration hr Q F H v u u',|T.weight D|)≤
      6*((r:ℝ)^2)^((ordinaryWheelRim D).support.toFinset.erase v).card*
        (Fintype.card V:ℝ)^(r^2-((ordinaryWheelRim D).support.toFinset.erase v).card) := by
  let S := (ordinaryWheelRim D).support.toFinset.erase v
  have hb (T : OrdinaryTransferConfiguration hr Q F H v u u') :
      |T.weight D|≤6*(if (↑S:Set V)⊆Set.range T.labels then (1:ℝ) else 0) := by
    by_cases hD : T.weight D=0
    · rw [hD,abs_zero]
      split_ifs <;> norm_num
    · rw [if_pos (T.erased_rim_subset D hD),mul_one]
      exact T.coefficient_bound D
  calc
    _ ≤ ∑ T : OrdinaryTransferConfiguration hr Q F H v u u',
        6*(if (↑S:Set V)⊆Set.range T.labels then (1:ℝ) else 0) :=
      Finset.sum_le_sum (fun T _ => hb T)
    _ = 6*∑ T : OrdinaryTransferConfiguration hr Q F H v u u',
        if (↑S:Set V)⊆Set.range T.labels then (1:ℝ) else 0 := by rw [Finset.mul_sum]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (ordinary_transfer_configuration_root_count
        (hr:=hr) (Q:=Q) (F:=F) (H:=H) (v:=v) (u:=u) (u':=u') S) (by norm_num : (0:ℝ)≤6)
      simpa only [mul_assoc] using hh

end Oberwolfach
