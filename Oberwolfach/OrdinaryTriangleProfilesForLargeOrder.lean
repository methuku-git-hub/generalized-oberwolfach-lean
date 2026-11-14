module

public import Oberwolfach.OrdinaryTriangleCommonGeometry
public import Oberwolfach.OrdinaryProfileBudgets

@[expose] public section

/-! In the triangular case the same fixed order threshold supplies the
numerical paired-absorber prerequisites from four-neighbourhood bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_profiles_for_large_order
    (β b B η L:ℝ) (hβ:0<β) (hL:0≤L):
    ∃ N:ℕ,∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V → ∀ (Q F:SimpleGraph V) (H:V→U→Prop),
      (∀ v,(F.degree v:ℝ)≤L) →
      (∀ u u' a b c d,β*Fintype.card V≤
        ((Finset.univ.filter (fun x=>H x u∧H x u'∧Q.Adj a x∧Q.Adj b x∧Q.Adj c x∧Q.Adj d x)).card:ℝ)) →
      ∀ w:∀ u u':U,u≠u'→LocalOrdinaryCycle Q F (Finset.univ.filter (fun v=>H v u∧H v u')) 3→ℝ,
      (∀ u u' (hne:u≠u') C,b/(Fintype.card V:ℝ)^2≤w u u' hne C ∧
        w u u' hne C≤B/(Fintype.card V:ℝ)^2) →
      (∀ u u' (hne:u≠u'),∀ v∈Finset.univ.filter (fun v=>H v u∧H v u'),
        |1-hypergraphWeightedDegree localOrdinaryVertices (w u u' hne) v|≤η) →
      Nonempty (OrdinaryCommonCycleProfiles Q F H 3 (fun (_:Unit)=>pairedAbsorberTemplate 3) β
        ((ordinaryLocalCountCoeff 2 β/2)^4) b B η) := by
  obtain ⟨N,hN⟩:=ordinary_profile_budgets 2 β L hβ
  refine ⟨max 1 N,?_⟩
  intro V U _ _ _ _ hn Q F H hF hfour w hw hdeg
  have hn1:0<Fintype.card V:=by omega
  letI:Nonempty V:=Fintype.card_pos_iff.mp hn1
  obtain ⟨hbudget,hnb,hnp⟩:=hN (Fintype.card V) (by omega)
  exact ⟨ordinary_triangle_profiles_from_four_neighbourhoods Q F H β b B η L hβ hL hF
    hfour hbudget hnb hnp w hw hdeg⟩
end Oberwolfach
