module

public import Oberwolfach.OrdinaryPairCommonGeometry
public import Oberwolfach.OrdinaryProfileBudgets

@[expose] public section

/-! The fixed order threshold supplies the numerical prerequisites of the
ordinary pair-profile construction. The graph and the fixed weights are
introduced only after that threshold; no profile existence is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_pair_profiles_for_large_order (m:ℕ) (hm:3≤m)
    (β b B η L:ℝ) (hβ:0<β) (hL:0≤L):
    ∃ N:ℕ,∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V → ∀ (Q F:SimpleGraph V) (H:V→U→Prop),
      (∀ v,(F.degree v:ℝ)≤L) →
      (∀ u u' v w,β*Fintype.card V≤
        (((Finset.univ.filter (fun a=>H a u∧H a u'))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ)) →
      ∀ w:∀ u u':U,u≠u'→LocalOrdinaryCycle Q F (Finset.univ.filter (fun v=>H v u∧H v u')) (m+1)→ℝ,
      (∀ u u' (hne:u≠u') C,b/(Fintype.card V:ℝ)^m≤w u u' hne C ∧
        w u u' hne C≤B/(Fintype.card V:ℝ)^m) →
      (∀ u u' (hne:u≠u'),∀ v∈Finset.univ.filter (fun v=>H v u∧H v u'),
        |1-hypergraphWeightedDegree localOrdinaryVertices (w u u' hne) v|≤η) →
      Nonempty (OrdinaryCommonCycleProfiles Q F H (m+1) (fun (_:Unit)=>pairedAbsorberTemplate (m+1)) β
        ((ordinaryLocalCountCoeff m β/2)^(m+2)) b B η) := by
  obtain ⟨N,hN⟩:=ordinary_profile_budgets m β L hβ
  refine ⟨max 1 N,?_⟩
  intro V U _ _ _ _ hn Q F H hF hpair w hw hdeg
  have hn1:0<Fintype.card V:=by omega
  letI:Nonempty V:=Fintype.card_pos_iff.mp hn1
  obtain ⟨hbudget,hnb,hnp⟩:=hN (Fintype.card V) (by omega)
  exact ⟨ordinary_common_profiles_from_pair_geometry m hm Q F H β b B η L hβ hL hF
    hpair hbudget hnb hnp w hw hdeg⟩
end Oberwolfach
