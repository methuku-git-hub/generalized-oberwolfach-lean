module

public import Oberwolfach.PermutationConflictDegree

@[expose] public section
/-! The physical edges excluded by either ordinary or marked distance
conditions have degree at most 6d+2 and at most (3d+1)n edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem permutationClose_mono_radius (π:Equiv.Perm V) (b c:ℕ) (hbc:b≤c) (x y:V):
    PermutationClose π b x y→PermutationClose π c x y:=by
  rintro (h|⟨j,h⟩)
  · exact Or.inl h
  · exact Or.inr ⟨⟨j.val,lt_of_lt_of_le j.isLt hbc⟩,h⟩

theorem permutationClose_apply_right (π:Equiv.Perm V) (b:ℕ) (x z:V):
    PermutationClose π b x z→PermutationClose π (b+1) x (π z):=by
  rintro (rfl|⟨j,hf|hr⟩)
  · right
    refine ⟨⟨0,by omega⟩,Or.inl ?_⟩
    simp
  · right
    refine ⟨⟨j.val+1,by omega⟩,Or.inl ?_⟩
    have hh:=congrArg π hf
    simpa only [pow_succ',Equiv.Perm.mul_apply] using hh
  · by_cases hzero:j.val=0
    · left
      have hh:=hr
      simp only [hzero,Nat.zero_add,pow_one] at hh
      exact hh.symm
    · right
      refine ⟨⟨j.val-1,by omega⟩,Or.inr ?_⟩
      have hp:(j.val-1)+1=j.val:=by omega
      rw [hp]
      simpa only [pow_succ,Equiv.Perm.mul_apply] using hr

def longPreparationIneligibleGraph (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ):SimpleGraph V where
  Adj x y:=P.Adj x y ∧ (PermutationClose π (3*d) x y ∨
    PermutationClose π (3*d) x (π.symm y) ∨ PermutationClose π (3*d) y (π.symm x))
  symm:=⟨by
    intro x y h
    refine ⟨h.1.symm,?_⟩
    rcases h.2 with h|h|h
    · exact Or.inl ((permutationClose_symm π (3*d) x y).mp h)
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩
  loopless:=⟨fun x h=>P.loopless.irrefl x h.1⟩

theorem long_preparation_ineligible_subgraph (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ):
    longPreparationIneligibleGraph P π d≤permutationConflictGraph π (3*d+1):=by
  intro x y h
  refine ⟨h.1.ne,?_⟩
  rcases h.2 with hc|hc|hc
  · exact permutationClose_mono_radius π (3*d) (3*d+1) (by omega) x y hc
  · simpa only [Equiv.apply_symm_apply] using permutationClose_apply_right π (3*d) x (π.symm y) hc
  · apply (permutationClose_symm π (3*d+1) y x).mp
    simpa only [Equiv.apply_symm_apply] using permutationClose_apply_right π (3*d) y (π.symm x) hc

theorem long_preparation_ineligible_degree (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (x:V):
    (longPreparationIneligibleGraph P π d).degree x≤6*d+2:=by
  have hsub:=long_preparation_ineligible_subgraph P π d
  have hn:(longPreparationIneligibleGraph P π d).neighborFinset x⊆
      (permutationConflictGraph π (3*d+1)).neighborFinset x:=by
    intro y hy
    simp only [SimpleGraph.mem_neighborFinset] at hy ⊢
    exact hsub hy
  have hc:=Finset.card_le_card hn
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hc
  have hh:=permutationConflictGraph_degree_le π (3*d+1) x
  omega

theorem long_preparation_ineligible_edge_count (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ):
    (longPreparationIneligibleGraph P π d).edgeFinset.card≤(3*d+1)*Fintype.card V:=by
  let F:=longPreparationIneligibleGraph P π d
  have hs:∑x:V,F.degree x≤∑_x:V,(6*d+2):=by
    apply Finset.sum_le_sum
    intro x _
    exact long_preparation_ineligible_degree P π d x
  have he:=F.sum_degrees_eq_twice_card_edges
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  simp only [Nat.cast_id] at hs
  have hprod:Fintype.card V*(6*d+2)=2*((3*d+1)*Fintype.card V):=by ring
  rw [hprod] at hs
  change F.edgeFinset.card≤(3*d+1)*Fintype.card V
  omega
end Oberwolfach
