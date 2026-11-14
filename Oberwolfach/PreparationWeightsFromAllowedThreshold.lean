module

public import Oberwolfach.MarkedPreparationLengthChoice
public import Oberwolfach.SelectedLengthsFractionalWeights
public import Oberwolfach.SelectedLengthsPositionalBudgets
public import Oberwolfach.TwoComponentLower

@[expose] public section
/-! The ordinary and marked weights used in long preparation exist with
constants and an order threshold chosen before the allowed length set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem preparation_weights_from_allowed_threshold
    (L:ℕ) (α:ℝ) (hα:0<α):
    ∃ m:ℕ,3≤m ∧ L≤m ∧ Even (m+1) ∧
    ∃ A BK:ℝ,0<A ∧ 0<BK ∧
    ∀ (K d:ℕ),2≤d→∀ (n:Fin K→ℕ),(∀ i,1≤n i)→∃ B:Fin K→ℝ,(∀ i,0<B i) ∧
    ∀ τ:ℝ,0<τ→∃ ε:ℝ,0<ε ∧ ε≤τ/4 ∧ ∃ N:ℕ,1≤N ∧
    ∀ (V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→
    ∀ (S:Finset (Fin K)) (Allowed:Set ℕ) (G:SimpleGraph V) (π:Equiv.Perm V) (D:ℝ),
      Allowed.Nonempty→(∀ r∈Allowed,3≤r)→
      ((Fintype.card V:ℝ)/2≤D)→D≤2*Fintype.card V→
      (∀ v,|(G.degree v:ℝ)-D|≤ε*Fintype.card V)→
      (∀ i:{i:Fin K // i∈S},n i.val+2∈Allowed)→
      (∀ v,(allowedThreshold Allowed+α)*Fintype.card V≤(G.degree v:ℝ))→
    ∃ w:∀ i:{i:Fin K // i∈S},OrdinaryCycle G (n i.val+2)→ℝ,
    ∃ wK:(Fin (m+1)→V)→ℝ,
      (∀ i C,0≤w i C ∧ w i C≤B i.val/(Fintype.card V:ℝ)^(n i.val)) ∧
      (∀ i x y,(∑ C,if C.val.val.Adj x y then w i C else 0)=if G.Adj x y then 1 else 0) ∧
      (∀ i:{i:Fin K // i∈S},5*((n i.val+2:ℕ):ℝ)^4*B i.val*(2*(3*d))/Fintype.card V≤τ ∧
        6*((n i.val+2:ℕ):ℝ)^4*B i.val*(2*(3*d))+ε*(Fintype.card V:ℝ)≤τ*D) ∧
      SuccessorSequenceWeightConditions G π (3*d) D τ A BK wK:=by
  classical
  obtain ⟨m,hm,hL,heven,hmargin⟩:=marked_preparation_length_choice (α/2) (by positivity) L
  obtain ⟨A,BK,hA,hBK,hmarked⟩:=marked_preparation_weight_choice m hm heven (α/2) (by positivity) hmargin
  refine ⟨m,hm,hL,heven,A,BK,hA,hBK,?_⟩
  intro K d hd n hn
  obtain ⟨B,hB,Nw,hNw,hordinary⟩:=selected_lengths_positive_fractional_weights K n hn α hα
  refine ⟨B,hB,?_⟩
  intro τ hτ
  obtain ⟨ε,hε,hετ,hmarked⟩:=hmarked τ hτ
  obtain ⟨Nb,hbudget⟩:=selected_lengths_positional_budgets K (3*d) (fun i=>n i+2) B (fun i=>(hB i).le) τ hτ
  have hb:2≤3*d:=by omega
  obtain ⟨Nm,hmarked⟩:=hmarked (3*d) hb
  refine ⟨ε,hε,hετ,max Nw (max Nb Nm),hNw.trans (le_max_left _ _),?_⟩
  intro V _ _ hN S Allowed G π D hAllowed hvalid hDlo hDhi hreg hmem hdeg
  have hthreshold:∀ i:{i:Fin K // i∈S},∀ v,
      (cycleThreshold (n i.val+2)+α)*Fintype.card V≤(G.degree v:ℝ):=by
    intro i v
    have hbdd:BddAbove (cycleThreshold '' Allowed):=by
      refine ⟨1,?_⟩
      rintro x ⟨r,hr,rfl⟩
      exact cycleThreshold_le_one r
    have hle:cycleThreshold (n i.val+2)≤allowedThreshold Allowed:=le_csSup hbdd ⟨_,hmem i,rfl⟩
    have hh:(cycleThreshold (n i.val+2)+α)*(Fintype.card V:ℝ)≤
      (allowedThreshold Allowed+α)*(Fintype.card V:ℝ):=
      mul_le_mul_of_nonneg_right (by linarith [hle]) (Nat.cast_nonneg _)
    exact hh.trans (hdeg v)
  obtain ⟨w,hw,he⟩:=hordinary V ((le_max_left _ _).trans hN) S G hthreshold
  have hhalf:1/2≤allowedThreshold Allowed:=allowedThreshold_half_le hAllowed hvalid
  have hmin:∀ v,(1/2+α/2)*(Fintype.card V:ℝ)≤(G.degree v:ℝ):=by
    intro v
    have hh:(1/2+α/2:ℝ)≤allowedThreshold Allowed+α:=by linarith
    exact (mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg _)).trans (hdeg v)
  obtain ⟨wK,hwK⟩:=hmarked V ((le_max_right _ _).trans ((le_max_right _ _).trans hN)) G π D hDlo hDhi hreg hmin
  refine ⟨w,wK,hw,he,?_,hwK⟩
  intro i
  have h:=hbudget (Fintype.card V) ((le_max_left _ _).trans ((le_max_right _ _).trans hN)) D ε hDlo hετ i.val
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using h
end Oberwolfach
