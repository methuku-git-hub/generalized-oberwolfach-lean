module

public import Oberwolfach.SelectedLengthsFractionalWeights
public import Oberwolfach.SelectedLengthsPositionalBudgets

@[expose] public section
/-! Fractional weights and both separation budgets are chosen uniformly
before selecting the short lengths used by the prescribed factors. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_lengths_weighted_positional_data
    (K d:ℕ) (n:Fin K→ℕ) (hn:∀ i,1≤n i) (α τ:ℝ) (hα:0<α) (hτ:0<τ):
    ∃ B:Fin K→ℝ,(∀ i,0<B i) ∧ ∃ N:ℕ,1≤N ∧
    ∀ (V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→
    ∀ (S:Finset (Fin K)) (G:SimpleGraph V) (D ε:ℝ),
      ((Fintype.card V:ℝ)/2≤D)→ε≤τ/4→
      (∀ i:{i:Fin K // i∈S},∀ v,(cycleThreshold (n i.val+2)+α)*Fintype.card V≤(G.degree v:ℝ))→
    ∃ w:∀ i:{i:Fin K // i∈S},OrdinaryCycle G (n i.val+2)→ℝ,
      (∀ i C,0≤w i C ∧ w i C≤B i.val/(Fintype.card V:ℝ)^(n i.val)) ∧
      (∀ i x y,(∑ C,if C.val.val.Adj x y then w i C else 0)=if G.Adj x y then 1 else 0) ∧
      (∀ i:{i:Fin K // i∈S},5*((n i.val+2:ℕ):ℝ)^4*B i.val*(2*(3*d))/Fintype.card V≤τ ∧
        6*((n i.val+2:ℕ):ℝ)^4*B i.val*(2*(3*d))+ε*(Fintype.card V:ℝ)≤τ*D):=by
  classical
  obtain ⟨B,hB,Nw,hNw,hw⟩:=selected_lengths_positive_fractional_weights K n hn α hα
  obtain ⟨Nb,hb⟩:=selected_lengths_positional_budgets K (3*d) (fun i=>n i+2) B (fun i=>(hB i).le) τ hτ
  refine ⟨B,hB,max Nw Nb,(le_max_left _ _ |>.trans' hNw),?_⟩
  intro V _ _ hN S G D ε hD hε hdeg
  obtain ⟨w,hw1,hw2⟩:=hw V ((le_max_left _ _).trans hN) S G hdeg
  refine ⟨w,hw1,hw2,?_⟩
  intro i
  have h:=hb (Fintype.card V) ((le_max_right _ _).trans hN) D ε hD hε i.val
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using h
end Oberwolfach
