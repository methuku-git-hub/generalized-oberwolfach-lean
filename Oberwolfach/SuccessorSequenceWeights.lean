module

public import Oberwolfach.SuccessorSeparatedWeights
public import Oberwolfach.SuccessorTupleRepresentation

@[expose] public section

/-! Successor weighting in ordinary ordered tuple coordinates. The edge
index j represents x_j x_{j+1}, except that the closing physical endpoint
is π(x₀). No coordinate multiplicities are introduced by the equivalence. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

structure SuccessorSequenceWeightConditions {V : Type*} [Fintype V] {c : ℕ}
    (G : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ) (D τ A B : ℝ)
    (w : (Fin c → V) → ℝ) : Prop where
  nonneg : ∀ f, 0 ≤ w f
  support : ∀ f, 0 < w f → SuccessorSequenceValid G π f ∧ PermutationSeparated π b f
  upper : ∀ f, w f ≤ B / (Fintype.card V : ℝ) ^ (c-2)
  lower : ∀ f, SuccessorSequenceValid G π f → PermutationSeparated π b f →
    A / (Fintype.card V : ℝ) ^ (c-2) ≤ w f
  edges : ∀ j x z, ¬ PermutationClose π b x z →
    G.Adj x (if j.val+1=c then π z else z) →
    1-τ ≤ (∑ f, if f j=x ∧ f (cycleNext j)=z then w f else 0) ∧
      (∑ f, if f j=x ∧ f (cycleNext j)=z then w f else 0) ≤ 1
  positions : ∀ j v, (1-τ)*D ≤ (∑ f, if f j=v then w f else 0) ∧
      (∑ f, if f j=v then w f else 0) ≤ D

theorem successor_sequence_weights_of_paired {V : Type*} [Fintype V] {k : ℕ}
    (G : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ) (D τ A B : ℝ)
    (w : (Fin (k+2) → V × V) → ℝ)
    (hw : SuccessorSeparatedWeightConditions G (fun i => choosePermutation π (closingInterface k i)) π b D τ A B w) :
    SuccessorSequenceWeightConditions G π b D τ A B
      (fun f => w ((pairSequenceEquiv k V).symm f)) := by
  have he : (k+2)*2-2=2*k+2 := by omega
  have hzero (i : Fin (k+2)) : (alternatingIndex i 0).val+1 ≠ (k+2)*2 := by
    change 0+2*i.val+1 ≠ (k+2)*2
    have hi := i.isLt
    omega
  have hone (i : Fin (k+2)) : (alternatingIndex i 1).val+1=(k+2)*2 ↔ i.val=k+1 := by
    change 1+2*i.val+1=(k+2)*2 ↔ i.val=k+1
    omega
  refine ⟨fun f => hw.nonneg _,?_,?_,?_,?_,?_⟩
  · intro f hf
    obtain ⟨hv,hs⟩ := hw.support _ hf
    have hv' := (successor_pair_sequence_valid G π _).mp hv
    have hs' := (pairSequence_separated π b _).mpr hs
    simpa only [Equiv.apply_symm_apply] using And.intro hv' hs'
  · intro f
    simpa only [he] using hw.upper ((pairSequenceEquiv k V).symm f)
  · intro f hv hs
    have hv' := (successor_pair_sequence_valid G π ((pairSequenceEquiv k V).symm f)).mpr
      (by simpa only [Equiv.apply_symm_apply] using hv)
    have hs' := (pairSequence_separated π b ((pairSequenceEquiv k V).symm f)).mp
      (by simpa only [Equiv.apply_symm_apply] using hs)
    simpa only [he] using hw.lower _ hv' hs'
  · have hl (i : Fin (k+2)) (x z : V) (hclose : ¬ PermutationClose π b x z)
        (hG : G.Adj x z) :
        1-τ ≤ (∑ f, if f (alternatingIndex i 0)=x ∧ f (cycleNext (alternatingIndex i 0))=z
          then w ((pairSequenceEquiv k V).symm f) else 0) ∧
        (∑ f, if f (alternatingIndex i 0)=x ∧ f (cycleNext (alternatingIndex i 0))=z
          then w ((pairSequenceEquiv k V).symm f) else 0) ≤ 1 := by
      rw [pairSequence_weight_incidence]
      simpa only [alternatingIndex_next_zero,pairSequenceEquiv_zero,pairSequenceEquiv_one,Prod.ext_iff]
        using hw.left i x z hclose hG
    have hr (i : Fin (k+2)) (x z : V) (hclose : ¬ PermutationClose π b x z)
        (hG : G.Adj x (choosePermutation π (closingInterface k i) z)) :
        1-τ ≤ (∑ f, if f (alternatingIndex i 1)=x ∧ f (cycleNext (alternatingIndex i 1))=z
          then w ((pairSequenceEquiv k V).symm f) else 0) ∧
        (∑ f, if f (alternatingIndex i 1)=x ∧ f (cycleNext (alternatingIndex i 1))=z
          then w ((pairSequenceEquiv k V).symm f) else 0) ≤ 1 := by
      rw [pairSequence_weight_incidence]
      simpa only [alternatingIndex_next_one,pairSequenceEquiv_zero,pairSequenceEquiv_one,Prod.mk.injEq]
        using hw.right i x z hclose hG
    intro j x z hclose hG
    obtain ⟨⟨i,a⟩,rfl⟩ := finProdFinEquiv.surjective j
    fin_cases a
    · apply hl i x z hclose
      change G.Adj x (if (alternatingIndex i 0).val+1=(k+2)*2 then π z else z) at hG
      simpa only [hzero,ite_false] using hG
    · apply hr i x z hclose
      change G.Adj x (if (alternatingIndex i 1).val+1=(k+2)*2 then π z else z) at hG
      simp only [hone] at hG
      by_cases hh : i.val=k+1 <;> simpa [choosePermutation,closingInterface,hh] using hG
  · have hl (i : Fin (k+2)) (v : V) :
        (1-τ)*D ≤ (∑ f, if f (alternatingIndex i 0)=v then w ((pairSequenceEquiv k V).symm f) else 0) ∧
        (∑ f, if f (alternatingIndex i 0)=v then w ((pairSequenceEquiv k V).symm f) else 0) ≤ D := by
      rw [pairSequence_weight_incidence]
      simpa only [pairSequenceEquiv_zero] using (hw.positions i v).1
    have hr (i : Fin (k+2)) (v : V) :
        (1-τ)*D ≤ (∑ f, if f (alternatingIndex i 1)=v then w ((pairSequenceEquiv k V).symm f) else 0) ∧
        (∑ f, if f (alternatingIndex i 1)=v then w ((pairSequenceEquiv k V).symm f) else 0) ≤ D := by
      rw [pairSequence_weight_incidence]
      simpa only [pairSequenceEquiv_one] using (hw.positions i v).2
    intro j v
    obtain ⟨⟨i,a⟩,rfl⟩ := finProdFinEquiv.surjective j
    fin_cases a
    · exact hl i v
    · exact hr i v

theorem successor_sequence_weight_existence (k : ℕ) (β : ℝ) (hβ : 0 < β) :
    ∀ τ : ℝ, 0 < τ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ b : ℕ, ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [Nonempty V], N ≤ Fintype.card V →
      ∀ (G : SimpleGraph V) (π : Equiv.Perm V) (D : ℝ),
      (Fintype.card V : ℝ)/2 ≤ D → D ≤ 2*Fintype.card V →
      (∀ v, |(G.degree v : ℝ)-D| ≤ ε₀*Fintype.card V) →
      (∀ v, (successorCycleRatio k + β)*Fintype.card V ≤ (G.degree v : ℝ)) →
      ∃ w : (Fin ((k+2)*2) → V) → ℝ, SuccessorSequenceWeightConditions G π b D τ
        (successorWeightLower k β) (successorWeightUpper k β) w := by
  intro τ hτ
  obtain ⟨ε₀,hε₀,hall⟩ := successor_separated_weight_existence k β hβ τ hτ
  refine ⟨ε₀,hε₀,?_⟩
  intro b
  obtain ⟨N,hN⟩ := hall b
  refine ⟨N,?_⟩
  intro V _ _ hn G π D hD hDup hnear hmin
  obtain ⟨w,hw⟩ := hN V hn G π (closingInterface k) D hD hDup hnear hmin
  exact ⟨_,successor_sequence_weights_of_paired G π b D τ _ _ w hw⟩

end Oberwolfach
