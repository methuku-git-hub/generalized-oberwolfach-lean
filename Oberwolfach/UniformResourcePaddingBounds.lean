module

public import Oberwolfach.UniformResourcePadding

@[expose] public section

/-! Degree and codegree hypotheses after adding private padding vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem uniformPadding_degree_bounds {V E : Type*} [Fintype E] [DecidableEq V]
    (R : E → Finset V) (k D : ℕ) (hD : 1≤D)
    (hdegree : ∀ v,0<Fintype.card (HypergraphEdgesAt R v) ∧
      Fintype.card (HypergraphEdgesAt R v)≤D) :
    ∀ v,0<Fintype.card (HypergraphEdgesAt (uniformPaddingIncidence R k) v) ∧
      Fintype.card (HypergraphEdgesAt (uniformPaddingIncidence R k) v)≤D := by
  classical
  rintro (v|⟨e,j⟩)
  · rw [uniformPadding_degree_original]
    exact hdegree v
  · simp only [HypergraphEdgesAt,Fintype.card_subtype,uniformPadding_private_mem]
    have heq : (Finset.univ.filter (fun f : E=>f=e)).card=1 := by
      apply Finset.card_eq_one.mpr
      refine ⟨e,?_⟩
      ext f
      simp
    rw [heq]
    exact ⟨by omega,hD⟩

theorem uniformPadding_codegree_bounds {V E : Type*} [Fintype E] [DecidableEq V]
    (R : E → Finset V) (k : ℕ) (κ : ℝ) (hκ : 1≤κ)
    (hcodeg : ∀ u v,u≠v →
      ((Finset.univ.filter (fun e=>u∈R e ∧ v∈R e)).card : ℝ)≤κ) :
    ∀ u v : UniformPaddingVertex R k,u≠v →
      ((Finset.univ.filter (fun e=>u∈uniformPaddingIncidence R k e ∧
        v∈uniformPaddingIncidence R k e)).card : ℝ)≤κ := by
  classical
  rintro (u|⟨e,j⟩) (v|⟨f,i⟩) hne
  · rw [uniformPadding_codegree_original]
    exact hcodeg u v (fun h=>hne (congrArg Sum.inl h))
  · apply le_trans (b:=(1 : ℝ)) _ hκ
    exact_mod_cast uniformPadding_codegree_private R k (Sum.inl u) f i
  · have heq : (Finset.univ.filter (fun f=>Sum.inr ⟨e,j⟩∈uniformPaddingIncidence R k f ∧
        Sum.inl v∈uniformPaddingIncidence R k f)).card=
      (Finset.univ.filter (fun f=>Sum.inl v∈uniformPaddingIncidence R k f ∧
        Sum.inr ⟨e,j⟩∈uniformPaddingIncidence R k f)).card := by
      congr 1
      ext f
      simp only [Finset.mem_filter,and_comm]
    rw [heq]
    apply le_trans (b:=(1 : ℝ)) _ hκ
    exact_mod_cast uniformPadding_codegree_private R k (Sum.inl v) e j
  · apply le_trans (b:=(1 : ℝ)) _ hκ
    exact_mod_cast uniformPadding_codegree_private R k (Sum.inr ⟨e,j⟩) f i

end Oberwolfach
