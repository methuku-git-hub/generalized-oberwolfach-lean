module

public import Oberwolfach.OrdinarySampledTriangleProfileProperty

@[expose] public section
/-! Consequences of the sampled four-root condition used by the relative absorber. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]
theorem ordinary_triangle_profile_absorber_geometry
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawWheelOutcome V U Γ Color)
    (pmin smin:ℝ) (j:Color) (β η a b:ℝ) [Nonempty U]
    (h:ordinarySampledTriangleProfileProperty P F π d σ pmin smin j β η a b):
    let Q:=rawWheelGraph P σ\F;
    let H:=rawWheelSpokes π d σ j;
    (∀ v w,β*Fintype.card V≤((Q.neighborFinset v∩Q.neighborFinset w).card:ℝ)) ∧
    (∀ u u' v w,β*Fintype.card V≤(((Finset.univ.filter (fun a=>H a u∧H a u'))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ)) ∧
    (∀ w x y z,β*Fintype.card V≤((Finset.univ.filter (fun a=>Q.Adj w a∧Q.Adj x a∧Q.Adj y a∧Q.Adj z a)).card:ℝ)) ∧
    (∀ u u' w x y z,β*Fintype.card V≤((Finset.univ.filter (fun a=>H a u∧H a u'∧Q.Adj w a∧Q.Adj x a∧Q.Adj y a∧Q.Adj z a)).card:ℝ)) := by
  intro Q H
  have h4: ∀ u u' w x y z,β*Fintype.card V≤((Finset.univ.filter (fun a=>H a u∧H a u'∧Q.Adj w a∧Q.Adj x a∧Q.Adj y a∧Q.Adj z a)).card:ℝ) := by
    intro u u' w x y z
    have hh := h.1 u u' w x y z
    convert hh using 1
    congr 1
    congr 1
    ext v
    simp [Q,H]
  let u:U:=Classical.choice inferInstance
  have hsubset (u u':U) (v w:V):
      Finset.univ.filter (fun a=>H a u∧H a u'∧Q.Adj v a∧Q.Adj w a∧Q.Adj v a∧Q.Adj w a) ⊆
      ((Finset.univ.filter (fun a=>H a u∧H a u'))∩Q.neighborFinset v∩Q.neighborFinset w) := by
    intro a ha
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at ha
    simp only [Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and,SimpleGraph.mem_neighborFinset]
    exact ⟨⟨⟨ha.1,ha.2.1⟩,ha.2.2.1⟩,ha.2.2.2.1⟩
  have hpair (u u':U) (v w:V):β*Fintype.card V≤
      (((Finset.univ.filter (fun a=>H a u∧H a u'))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ) := by
    apply le_trans (h4 u u' v w v w)
    exact_mod_cast Finset.card_le_card (hsubset u u' v w)
  refine ⟨?_,hpair,?_,h4⟩
  · intro v w
    apply le_trans (hpair u u v w)
    have hsub : ((Finset.univ.filter (fun a=>H a u∧H a u))∩Q.neighborFinset v∩Q.neighborFinset w) ⊆ Q.neighborFinset v∩Q.neighborFinset w := by
      intro a ha
      simp only [Finset.mem_inter] at ha ⊢
      exact ⟨ha.1.2,ha.2⟩
    exact_mod_cast Finset.card_le_card hsub
  · intro w x y z
    apply le_trans (h4 u u w x y z)
    have hsub : Finset.univ.filter (fun a=>H a u∧H a u∧Q.Adj w a∧Q.Adj x a∧Q.Adj y a∧Q.Adj z a) ⊆ Finset.univ.filter (fun a=>Q.Adj w a∧Q.Adj x a∧Q.Adj y a∧Q.Adj z a) := by
      intro a ha
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at ha ⊢
      exact ⟨ha.2.2.1,ha.2.2.2.1,ha.2.2.2.2.1,ha.2.2.2.2.2⟩
    exact_mod_cast Finset.card_le_card hsub
end Oberwolfach
