module

public import Oberwolfach.SuccessorWeightsTheorem

@[expose] public section
/-! Fixed marked weight constants and an order threshold, with a degree
tolerance that also fits the ordinary positional error budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_preparation_weight_choice
    (m:ℕ) (hm:3≤m) (heven:Even (m+1)) (γ:ℝ) (hγ:0<γ)
    (hmargin:((m+1:ℕ):ℝ)/(2*((m+1:ℕ):ℝ)-2)+γ/2≤1/2+γ):
    ∃ A B:ℝ,0<A ∧ 0<B ∧ ∀ τ:ℝ,0<τ→∃ ε:ℝ,0<ε ∧ ε≤τ/4 ∧
      ∀ b:ℕ,2≤b→∃ N:ℕ,∀ (V:Type) [Fintype V],N≤Fintype.card V→
      ∀ (G:SimpleGraph V) (π:Equiv.Perm V) (D:ℝ),
      (Fintype.card V:ℝ)/2≤D→D≤2*Fintype.card V→
      (∀ v,|(G.degree v:ℝ)-D|≤ε*Fintype.card V)→
      (∀ v,(1/2+γ)*Fintype.card V≤(G.degree v:ℝ))→
      ∃ w:(Fin (m+1)→V)→ℝ,SuccessorSequenceWeightConditions G π b D τ A B w:=by
  obtain ⟨A,B,hA,hB,hweight⟩:=successor_weights_theorem (m+1) (by omega) heven (γ/2) (by positivity)
  refine ⟨A,B,hA,hB,?_⟩
  intro τ hτ
  obtain ⟨ε₀,hε₀,hweight⟩:=hweight τ hτ
  let ε:=min ε₀ (τ/4)
  have hε:0<ε:=lt_min hε₀ (by positivity)
  refine ⟨ε,hε,min_le_right _ _,?_⟩
  intro b hb
  obtain ⟨N,hN⟩:=hweight b hb
  refine ⟨N,?_⟩
  intro V _ hn G π D hDlo hDhi hnear hmin
  apply hN V hn G π D hDlo hDhi
  · intro v
    exact (hnear v).trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  · intro v
    exact (mul_le_mul_of_nonneg_right hmargin (Nat.cast_nonneg _)).trans (hmin v)
end Oberwolfach
