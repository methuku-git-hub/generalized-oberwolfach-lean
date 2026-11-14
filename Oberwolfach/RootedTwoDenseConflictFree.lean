module

public import Oberwolfach.RootedAdmissibleDensity
public import Oberwolfach.RootedDenseSetScales
public import Oberwolfach.CoordinateLocalLemma

@[expose] public section
/-! One uniform rooted sample satisfies degree lower bounds in two graphs
and avoids every edge of a bounded-degree conflict graph. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rooted_two_dense_conflict_free (s:ℕ) (α:ℝ) (hα:0<α):
    ∃ K:ℕ,∀ k:ℕ,K≤k→∀ L:ℝ,0≤L→∃ N:ℕ,
    ∀ (V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→
    ∀ (P₁ P₂ F:SimpleGraph V) (T:Finset V),T.card=s→∀ δ₁ δ₂:ℝ,
    (∀ v,(δ₁+α)*Fintype.card V≤(P₁.degree v:ℝ))→
    (∀ v,(δ₂+α)*Fintype.card V≤(P₂.degree v:ℝ))→
    (∀ v,(F.degree v:ℝ)≤L)→(∀ x∈T,∀ y∈T,¬F.Adj x y)→
    ∃ R:RootedSubset V T k,
      (∀ v∈R.val.val,(δ₁+α/2)*(s+k:ℝ)<((P₁.neighborFinset v∩R.val.val).card:ℝ)) ∧
      (∀ v∈R.val.val,(δ₂+α/2)*(s+k:ℝ)<((P₂.neighborFinset v∩R.val.val).card:ℝ)) ∧
      (∀ x∈R.val.val,∀ y∈R.val.val,¬F.Adj x y):=by
  obtain ⟨K,hK⟩:=rooted_dense_set_scales s α hα
  refine ⟨K,?_⟩
  intro k hk L hL
  obtain ⟨hk2,hroots,hfail,hN⟩:=hK k hk
  obtain ⟨N,hN⟩:=hN L hL
  refine ⟨N,?_⟩
  intro V _ _ hn P₁ P₂ F T hT δ₁ δ₂ hP₁ hP₂ hF hTfree
  have hsize:T.card+k≤Fintype.card V:=by
    have hh:=(hN (Fintype.card V) hn).2.1
    omega
  have hconf:= (hN (Fintype.card V) hn).2.2
  letI:Nonempty (RootedSubset V T k):=rootedSubset_nonempty T k hsize
  let μ:=FiniteLaw.uniform (RootedSubset V T k)
  let E₁:RootedSubset V T k→Prop:=fun R=>
    (∀ v∈R.val.val,(δ₁+α/2)*(s+k:ℝ)<((P₁.neighborFinset v∩R.val.val).card:ℝ)) ∧
    (∀ x∈R.val.val,∀ y∈R.val.val,¬F.Adj x y)
  let E₂:RootedSubset V T k→Prop:=fun R=>∀ v∈R.val.val,
    (δ₂+α/2)*(s+k:ℝ)<((P₂.neighborFinset v∩R.val.val).card:ℝ)
  have hroots':(T.card:ℝ)+1≤α*(T.card+k:ℝ)/4:=by simpa [hT] using hroots
  have hp₁:=rootedSubset_dense_conflict_free_probability P₁ F T k hsize hk2 δ₁ α L hα hP₁ hF hTfree hroots'
  have hp₂:=rootedSubset_dense_conflict_free_probability P₂ ⊥ T k hsize hk2 δ₂ α 0 hα hP₂
    (by intro v;simp) (by intro x hx y hy;simp) hroots'
  have hprob₁:(1/2:ℝ)≤μ.probability E₁:=by
    have hh:(1-2*(s+k:ℝ)*Real.exp (-α^2*(s+k:ℝ)/8)-
        L*(2*(s:ℝ)*((k:ℝ)/(Fintype.card V-s:ℕ))+Fintype.card V*((k:ℝ)/(Fintype.card V-s:ℕ))^2))
        ≤μ.probability E₁:=by simpa only [hT,μ,E₁] using hp₁
    linarith
  have hprob₂:(1-(1/4:ℝ))≤μ.probability E₂:=by
    have hh:(1-2*(s+k:ℝ)*Real.exp (-α^2*(s+k:ℝ)/8))≤μ.probability E₂:=by
      simpa only [zero_mul,sub_zero,hT,SimpleGraph.bot_adj,not_false_eq_true,implies_true,and_true,μ,E₂] using hp₂
    linarith
  have hi:=finiteLaw_good_intersection μ E₁ E₂ (1/4) hprob₂
  obtain ⟨R,_,hR⟩:=finiteLaw_positive_event_exists μ (fun R=>E₁ R∧E₂ R) (by linarith)
  exact ⟨R,hR.1.1,hR.2,hR.1.2⟩
end Oberwolfach
