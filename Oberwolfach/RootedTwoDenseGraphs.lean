module

public import Oberwolfach.RootedAdmissibleDensity
public import Oberwolfach.RootedDenseSetScales
public import Oberwolfach.CoordinateLocalLemma

@[expose] public section
/-! A single uniform rooted subset simultaneously inherits lower-degree
bounds in two graphs. It can be applied to a graph and its complement. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rooted_two_dense_graphs_exist (s:ℕ) (α:ℝ) (hα:0<α):
    ∃ K:ℕ,∀ k:ℕ,K≤k→∃ N:ℕ,
    ∀ (V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→
    ∀ (P₁ P₂:SimpleGraph V) (T:Finset V),T.card=s→∀ δ₁ δ₂:ℝ,
    (∀ v,(δ₁+α)*Fintype.card V≤(P₁.degree v:ℝ))→
    (∀ v,(δ₂+α)*Fintype.card V≤(P₂.degree v:ℝ))→
    ∃ R:RootedSubset V T k,
      (∀ v∈R.val.val,(δ₁+α/2)*(s+k:ℝ)<((P₁.neighborFinset v∩R.val.val).card:ℝ)) ∧
      (∀ v∈R.val.val,(δ₂+α/2)*(s+k:ℝ)<((P₂.neighborFinset v∩R.val.val).card:ℝ)):=by
  obtain ⟨K,hK⟩:=rooted_dense_set_scales s α hα
  refine ⟨K,?_⟩
  intro k hk
  obtain ⟨hk2,hroots,hfail,hN⟩:=hK k hk
  obtain ⟨N,hN⟩:=hN 0 (le_refl _)
  refine ⟨N,?_⟩
  intro V _ _ hn P₁ P₂ T hT δ₁ δ₂ hP₁ hP₂
  have hsize:T.card+k≤Fintype.card V:=by
    have hh:=(hN (Fintype.card V) hn).2.1
    omega
  letI:Nonempty (RootedSubset V T k):=rootedSubset_nonempty T k hsize
  let μ:=FiniteLaw.uniform (RootedSubset V T k)
  let E₁:RootedSubset V T k→Prop:=fun R=>∀ v∈R.val.val,
    (δ₁+α/2)*(s+k:ℝ)<((P₁.neighborFinset v∩R.val.val).card:ℝ)
  let E₂:RootedSubset V T k→Prop:=fun R=>∀ v∈R.val.val,
    (δ₂+α/2)*(s+k:ℝ)<((P₂.neighborFinset v∩R.val.val).card:ℝ)
  have hroots':(T.card:ℝ)+1≤α*(T.card+k:ℝ)/4:=by simpa [hT] using hroots
  have hp₁:=rootedSubset_dense_conflict_free_probability P₁ ⊥ T k hsize hk2 δ₁ α 0 hα hP₁
    (by intro v;simp) (by intro x hx y hy;simp) hroots'
  have hp₂:=rootedSubset_dense_conflict_free_probability P₂ ⊥ T k hsize hk2 δ₂ α 0 hα hP₂
    (by intro v;simp) (by intro x hx y hy;simp) hroots'
  have hprob₁:(3/4:ℝ)≤μ.probability E₁:=by
    have hh:(1-2*(s+k:ℝ)*Real.exp (-α^2*(s+k:ℝ)/8))≤μ.probability E₁:=by
      simpa only [zero_mul,sub_zero,hT,SimpleGraph.bot_adj,not_false_eq_true,implies_true,and_true,μ,E₁] using hp₁
    linarith
  have hprob₂:(1-(1/4:ℝ))≤μ.probability E₂:=by
    have hh:(1-2*(s+k:ℝ)*Real.exp (-α^2*(s+k:ℝ)/8))≤μ.probability E₂:=by
      simpa only [zero_mul,sub_zero,hT,SimpleGraph.bot_adj,not_false_eq_true,implies_true,and_true,μ,E₂] using hp₂
    linarith
  have hi:=finiteLaw_good_intersection μ E₁ E₂ (1/4) hprob₂
  obtain ⟨R,_,hR⟩:=finiteLaw_positive_event_exists μ (fun R=>E₁ R∧E₂ R) (by linarith)
  exact ⟨R,hR.1,hR.2⟩
end Oberwolfach
