module

public import Oberwolfach.OrdinaryCommonProfilesFromGeometry

@[expose] public section

/-! The two-root common-neighbourhood input needed by the paired-absorber
count follows from the concrete two-neighbourhood hypotheses of the
ordinary relative-host construction, including sets of zero or one root. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Nonempty V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_pair_common_geometry (Q:SimpleGraph V) (H:V→U→Prop) (β:ℝ)
    (hpair:∀ u u' v w,β*Fintype.card V≤
      (((Finset.univ.filter (fun a=>H a u∧H a u'))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ)):
    ∀ u u':U,∀ S:Finset V,S.card≤2→
      β*Fintype.card V≤((common (Finset.univ.filter (fun v=>H v u∧H v u')) S
        (fun x=>Q.neighborFinset x)).card:ℝ) := by
  intro u u' S hS
  have hpad:∃ v w:V,S⊆{v,w}:=by
    by_cases h:S.Nonempty
    · obtain ⟨v,hv⟩:=h
      have hc:(S.erase v).card≤1:=by
        have he:=Finset.card_erase_of_mem hv
        omega
      obtain ⟨w,hw⟩:=Finset.card_le_one_iff_subset_singleton.mp hc
      refine ⟨v,w,?_⟩
      intro x hx
      by_cases h:x=v
      · simp [h]
      · have hx':x∈S.erase v:=Finset.mem_erase.mpr ⟨h,hx⟩
        have hxw:=hw hx'
        simpa using Or.inr (Finset.mem_singleton.mp hxw)
    · let v:V:=Classical.arbitrary V
      exact ⟨v,v,by simp [Finset.not_nonempty_iff_eq_empty.mp h]⟩
  obtain ⟨v,w,hsub⟩:=hpad
  have hinc:
      (Finset.univ.filter (fun a=>H a u∧H a u'))∩Q.neighborFinset v∩Q.neighborFinset w ⊆
      common (Finset.univ.filter (fun a=>H a u∧H a u')) S (fun x=>Q.neighborFinset x) := by
    intro x hx
    simp only [Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and,SimpleGraph.mem_neighborFinset] at hx
    simp only [common,Finset.mem_filter,Finset.mem_univ,true_and]
    refine ⟨hx.1.1,?_⟩
    intro a ha
    have ha':a=v∨a=w:=by simpa using hsub ha
    rcases ha' with rfl|rfl
    · simpa only [SimpleGraph.mem_neighborFinset] using hx.1.2
    · simpa only [SimpleGraph.mem_neighborFinset] using hx.2
  exact (hpair u u' v w).trans (by exact_mod_cast Finset.card_le_card hinc)

/-- Construct the profiles for cycle lengths at least four directly from
    the two-neighbourhood hypotheses used by the ordinary host absorber. -/
def ordinary_common_profiles_from_pair_geometry
    (m:ℕ) (hm:3≤m) (Q F:SimpleGraph V) (H:V→U→Prop)
    (β b B η L:ℝ) (hβ:0<β) (hL:0≤L)
    (hF:∀ v,(F.degree v:ℝ)≤L)
    (hpair:∀ u u' v w,β*Fintype.card V≤
      (((Finset.univ.filter (fun a=>H a u∧H a u'))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hbudget:(m+3:ℝ)*(L+1)≤β/2*Fintype.card V)
    (hnb:2*(m+1:ℝ)^2≤ordinaryLocalCountCoeff m β*Fintype.card V)
    (hnp:2*(m:ℝ)*(2*(m+1)+(m+1)*m)≤ordinaryLocalCountCoeff m β*Fintype.card V)
    (w:∀ u u':U,u≠u'→LocalOrdinaryCycle Q F (Finset.univ.filter (fun v=>H v u∧H v u')) (m+1)→ℝ)
    (hw:∀ u u' (hne:u≠u') C,b/(Fintype.card V:ℝ)^m≤w u u' hne C ∧
      w u u' hne C≤B/(Fintype.card V:ℝ)^m)
    (hdeg:∀ u u' (hne:u≠u'),∀ v∈Finset.univ.filter (fun v=>H v u∧H v u'),
      |1-hypergraphWeightedDegree localOrdinaryVertices (w u u' hne) v|≤η) :
    OrdinaryCommonCycleProfiles Q F H (m+1) (fun (_:Unit)=>pairedAbsorberTemplate (m+1)) β
      ((ordinaryLocalCountCoeff m β/2)^(m+2)) b B η := by
  let v:V:=Classical.arbitrary V
  have hsize:∀ u u':U,u≠u'→β*Fintype.card V≤
      ((Finset.univ.filter (fun x=>H x u∧H x u')).card:ℝ):=by
    intro u u' _
    exact (hpair u u' v v).trans (by
      exact_mod_cast Finset.card_le_card (Finset.inter_subset_left.trans Finset.inter_subset_left))
  have hcommon:∀ u u':U,u≠u'→∀ S:Finset V,S.card≤(if m=2 then 3 else 2)→
      β*Fintype.card V≤((common (Finset.univ.filter (fun x=>H x u∧H x u')) S
        (fun x=>Q.neighborFinset x)).card:ℝ):=by
    intro u u' _ S hS
    apply ordinary_pair_common_geometry Q H β hpair u u' S
    simpa [show m≠2 by omega] using hS
  exact ordinary_common_profiles_from_geometry m (by omega) Q F H β b B η β L hβ hL hF
    hsize hcommon hbudget hnb hnp w hw hdeg

end Oberwolfach
