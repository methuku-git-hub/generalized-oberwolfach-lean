module

public import Oberwolfach.ClassInsertionBudget
public import Oberwolfach.OrientationDisagreementGraph
public import Oberwolfach.GreedyGraphCandidates

@[expose] public section
/-! Regularisation edits and orientation corrections fit one physical deletion.
A surviving sampled arc that belongs to the sampled class is then an arc of
the corrected balanced class. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem class_correction_matching_deletion_contains_edits
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color]
    (P S₀ S D₀:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (M:V→V→ℕ) (ξ δ η:ℝ)
    (hS₀P:S₀≤P)
    (hedit:∀v,((changed (S₀.neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*Fintype.card V)
    (hcorrect:∀v,((orientationDisagreementGraph S₀ (fun e=>(ω (Sum.inl e)).2) M).degree v:ℝ)≤δ*Fintype.card V)
    (hD₀:∀v,(D₀.degree v:ℝ)≤η*Fintype.card V):
    ∃Del:SimpleGraph V,D₀≤Del ∧ (S₀\S)≤Del ∧
      orientationDisagreementGraph S₀ (fun e=>(ω (Sum.inl e)).2) M≤Del ∧
      (∀v,(Del.degree v:ℝ)≤(η+ξ+δ)*Fintype.card V) ∧
      (∀x y,S₀.Adj x y→¬Del.Adj x y→S.Adj x y) ∧
      (∀x y,S₀.Adj x y → rawMixedPhysicalArc P π d
        (fun e=>rawExpandedApproximateCollapse e (ω e)) x y→¬Del.Adj x y→M x y=1):=by
  let C:=orientationDisagreementGraph S₀ (fun e=>(ω (Sum.inl e)).2) M
  let Del:=D₀⊔((S₀\S)⊔C)
  refine ⟨Del,le_sup_left,le_trans le_sup_left le_sup_right,le_trans le_sup_right le_sup_right,?_,?_,?_⟩
  · intro v
    have hdel:((Del.degree v:ℝ)≤(D₀.degree v:ℝ)+((S₀\S)⊔C).degree v):=by
      have hh:=graph_degree_sup_le D₀ ((S₀\S)⊔C) v
      simp only [← SimpleGraph.ncard_neighborSet] at hh ⊢
      exact_mod_cast hh
    have hsup:((((S₀\S)⊔C).degree v:ℝ)≤((S₀\S).degree v:ℝ)+C.degree v):=by
      have hh:=graph_degree_sup_le (S₀\S) C v
      simp only [← SimpleGraph.ncard_neighborSet] at hh ⊢
      exact_mod_cast hh
    have hdiff:(((S₀\S).degree v:ℝ)≤ξ*Fintype.card V):=by
      have hh:=class_insertion_degree_le_edits S S₀ Finset.univ v
      have hrestr:spanningRestriction (S₀\S) Finset.univ=S₀\S:=by
        ext x y; simp [spanningRestriction_adj]
      rw [hrestr] at hh
      have hc:((changed (S.neighborFinset v) (S₀.neighborFinset v)).card:ℝ)≤ξ*Fintype.card V:=by
        simpa [changed,Finset.union_comm] using hedit v
      have hh':(((S₀\S).degree v:ℝ)≤(changed (S.neighborFinset v) (S₀.neighborFinset v)).card):=by
        simp only [← SimpleGraph.ncard_neighborSet] at hh ⊢
        exact_mod_cast hh
      exact hh'.trans hc
    dsimp [C] at hsup
    simp only [← SimpleGraph.ncard_neighborSet] at hdel hsup hdiff hD₀ hcorrect ⊢
    nlinarith [hD₀ v,hcorrect v]
  · intro x y hxy hnot
    by_contra hnotS
    exact hnot (Or.inr (Or.inl ⟨hxy,hnotS⟩))
  · intro x y hxy harc hnot
    have hs:=expanded_approximate_arc_uses_sampled_orientation P π d ω x y harc
    have hp:P.Adj x y:=hS₀P hxy
    have hs₀:sampledOrientation S₀ (fun e=>(ω (Sum.inl e)).2) x y=1:=by
      simpa [sampledOrientation,hxy,hp] using hs
    by_contra hm
    apply hnot
    exact Or.inr (Or.inr ⟨hxy,Or.inl (by simpa [hs₀] using hm)⟩)
end Oberwolfach
