module

public import Oberwolfach.PaddedSelectedCycleWeights
public import Oberwolfach.PreparationWeightsUniformD

@[expose] public section
/-! Choose all constants before the allowed set and pad unused lengths by
zero, without changing the exact edge sums on retained lengths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem preparation_padded_weights_from_allowed_threshold_uniform_d
    (L:ℕ) (α:ℝ) (hα:0<α):
    ∃ m:ℕ,3≤m ∧ L≤m ∧ Even (m+1) ∧
    ∃ A BK:ℝ,0<A ∧ 0<BK ∧
    ∀ (K:ℕ) (n:Fin K→ℕ),(∀ i,1≤n i)→∃ B:Fin K→ℝ,(∀ i,0<B i) ∧
    ∀ (d:ℕ),2≤d→∀ τ:ℝ,0<τ→∃ ε:ℝ,0<ε ∧ ε≤τ/4 ∧ ∃ N:ℕ,1≤N ∧
    ∀ (V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→
    ∀ (S:Finset (Fin K)) (Allowed:Set ℕ) (G:SimpleGraph V) (π:Equiv.Perm V) (D:ℝ),
      Allowed.Nonempty→(∀ r∈Allowed,3≤r)→
      ((Fintype.card V:ℝ)/2≤D)→D≤2*Fintype.card V→
      (∀ v,|(G.degree v:ℝ)-D|≤ε*Fintype.card V)→
      (∀ i:{i:Fin K // i∈S},n i.val+2∈Allowed)→
      (∀ v,(allowedThreshold Allowed+α)*Fintype.card V≤(G.degree v:ℝ))→
    ∃ w:∀ i:Fin K,OrdinaryCycle G (n i+2)→ℝ,
    ∃ wK:(Fin (m+1)→V)→ℝ,
      (∀ i C,0≤w i C ∧ w i C≤B i/(Fintype.card V:ℝ)^(n i)) ∧
      (∀ i:↥S,∀ x y,(∑ C,if C.val.val.Adj x y then w i.val C else 0)=if G.Adj x y then 1 else 0) ∧
      (∀ i∉S,∀ C,w i C=0) ∧
      (∀ i:↥S,5*((n i.val+2:ℕ):ℝ)^4*B i.val*(2*(3*d))/Fintype.card V≤τ ∧
        6*((n i.val+2:ℕ):ℝ)^4*B i.val*(2*(3*d))+ε*(Fintype.card V:ℝ)≤τ*D) ∧
      SuccessorSequenceWeightConditions G π (3*d) D τ A BK wK:=by
  obtain ⟨m,hm,hL,heven,A,BK,hA,hBK,hcore⟩:=preparation_weights_from_allowed_threshold_uniform_d L α hα
  refine ⟨m,hm,hL,heven,A,BK,hA,hBK,?_⟩
  intro K n hn
  obtain ⟨B,hB,hcore⟩:=hcore K n hn
  refine ⟨B,hB,?_⟩
  intro d hd τ hτ
  have hcore:=hcore d hd
  obtain ⟨ε,hε,hετ,N,hN,hcore⟩:=hcore τ hτ
  refine ⟨ε,hε,hετ,N,hN,?_⟩
  intro V _ _ hnV S Allowed G π D hAllowed hvalid hDlo hDhi hreg hmem hdeg
  obtain ⟨w,wK,hw,he,hbudget,hwK⟩:=hcore V hnV S Allowed G π D hAllowed hvalid hDlo hDhi hreg hmem hdeg
  obtain ⟨wfull,hfull,hOn,hExact,hOff⟩:=padded_selected_cycle_weights G K n B (fun i=>(hB i).le) S w hw he
  exact ⟨wfull,wK,hfull,hExact,hOff,hbudget,hwK⟩
end Oberwolfach
