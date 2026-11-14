module

public import Oberwolfach.OrdinaryIsolatorCandidates

@[expose] public section

/-! Exact conversion of the potential survival sum to physical isolator
configurations, including deletion of all conflict edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]

def ordinaryIsolatorDeleteConflictsEquiv (P Q F : SimpleGraph V) (H : V → U → Prop)
    (k : ℕ) (θ α : ℝ) (x y : V) (u : U) :
    {C : OrdinaryIsolatorConfiguration P Q F H k θ α x y // C.hub=u} ≃
    {C : OrdinaryIsolatorConfiguration P (Q\F) F H k θ α x y // C.hub=u} where
  toFun C := ⟨{ C.val with
    rim_edges := by
      intro z t hzt
      have hh := (spanningRestriction_adj P C.val.vertices.val z t).mp hzt
      exact ⟨C.val.rim_edges hzt,C.val.independent z hh.2.1 t hh.2.2⟩ },C.property⟩
  invFun C := ⟨{ C.val with
    rim_edges := by
      intro z t hzt
      exact (C.val.rim_edges hzt).1 },C.property⟩
  left_inv C := by apply Subtype.ext;apply OrdinaryIsolatorConfiguration.encoding_injective;rfl
  right_inv C := by apply Subtype.ext;apply OrdinaryIsolatorConfiguration.encoding_injective;rfl


theorem rootedInducedSurvivalSum_card {I : Type*} [Fintype I] {k : ℕ}
    (P : SimpleGraph V) (S : I → FixedSubset V k) (root : Sym2 V) (σ : Sym2 V → Bool) :
    rootedInducedSurvivalSum P S root σ=
      (Fintype.card {i : I // ∀ e∈rootOmittedInducedEdges P (S i).val root,σ e=true}:ℝ)/
        (Fintype.card V:ℝ)^(k-2) := by
  unfold rootedInducedSurvivalSum
  simp_rw [patternValue_indicator]
  rw [← Finset.mul_sum]
  rw [Fintype.card_subtype]
  simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [div_eq_mul_inv,mul_comm]
  simp only [one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl


theorem ordinary_isolator_potential_count_eq (P F : SimpleGraph V) (H : V → U → Prop)
    (k : ℕ) (θ α : ℝ) (x y : V) (u : U) (σ : Sym2 V → Bool)
    (hroot : (retainedGraph P σ).Adj x y) (hx : H x u) (hy : H y u) :
    rootedInducedSurvivalSum P
      (fun S : OrdinaryIsolatorCandidate P F H k θ α x y u=>S.val) s(x,y) σ=
      (Fintype.card {C : OrdinaryIsolatorConfiguration P (retainedGraph P σ\F) F H k θ α x y // C.hub=u}:ℝ)/
        (Fintype.card V:ℝ)^(k-2) := by
  rw [rootedInducedSurvivalSum_card]
  congr 1
  exact_mod_cast Fintype.card_congr ((ordinaryIsolatorCandidateEquiv P F H k θ α x y u σ hroot hx hy).trans
    (ordinaryIsolatorDeleteConflictsEquiv P (retainedGraph P σ) F H k θ α x y u))

end Oberwolfach
