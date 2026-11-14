module

public import Oberwolfach.OrdinaryCommonProfilesFromGeometry

@[expose] public section

/-! Four-root common-neighbourhood estimates also supply the zero- through
three-root estimates required by the triangular paired-absorber count. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Nonempty V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_common_geometry (Q:SimpleGraph V) (H:V→U→Prop) (β:ℝ)
    (hfour:∀ u u' a b c d,β*Fintype.card V≤
      ((Finset.univ.filter (fun x=>H x u∧H x u'∧Q.Adj a x∧Q.Adj b x∧Q.Adj c x∧Q.Adj d x)).card:ℝ)):
    ∀ u u':U,∀ S:Finset V,S.card≤3→
      β*Fintype.card V≤((common (Finset.univ.filter (fun v=>H v u∧H v u')) S
        (fun x=>Q.neighborFinset x)).card:ℝ) := by
  intro u u' S hS
  have hpad:∃ a b c:V,S⊆{a,b,c}:=by
    by_cases h:S.Nonempty
    · obtain ⟨a,ha⟩:=h
      let T:=S.erase a
      have ht:T.card≤2:=by dsimp [T];have he:=Finset.card_erase_of_mem ha;omega
      by_cases hT:T.Nonempty
      · obtain ⟨b,hb⟩:=hT
        have hc:(T.erase b).card≤1:=by have he:=Finset.card_erase_of_mem hb;omega
        obtain ⟨c,hc⟩:=Finset.card_le_one_iff_subset_singleton.mp hc
        refine ⟨a,b,c,?_⟩
        intro x hx
        by_cases ha':x=a
        · simp [ha']
        · have hxT:x∈T:=Finset.mem_erase.mpr ⟨ha',hx⟩
          by_cases hb':x=b
          · simp [hb']
          · have hxc:=hc (Finset.mem_erase.mpr ⟨hb',hxT⟩)
            simp [Finset.mem_singleton.mp hxc]
      · let b:V:=Classical.arbitrary V
        refine ⟨a,b,b,?_⟩
        intro x hx
        have he:T=∅:=Finset.not_nonempty_iff_eq_empty.mp hT
        by_cases h:x=a
        · simp [h]
        · have hxT:x∈T:=Finset.mem_erase.mpr ⟨h,hx⟩
          simp [he] at hxT
    · let a:V:=Classical.arbitrary V
      exact ⟨a,a,a,by simp [Finset.not_nonempty_iff_eq_empty.mp h]⟩
  obtain ⟨a,b,c,hsub⟩:=hpad
  have hinc:(Finset.univ.filter (fun x=>H x u∧H x u'∧Q.Adj a x∧Q.Adj b x∧Q.Adj c x∧Q.Adj c x)) ⊆
      common (Finset.univ.filter (fun v=>H v u∧H v u')) S (fun x=>Q.neighborFinset x) := by
    intro x hx
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hx
    simp only [common,Finset.mem_filter,Finset.mem_univ,true_and]
    refine ⟨⟨hx.1,hx.2.1⟩,?_⟩
    intro v hv
    have hv':v=a∨v=b∨v=c:=by simpa using hsub hv
    rcases hv' with rfl|rfl|rfl
    · simpa only [SimpleGraph.mem_neighborFinset] using hx.2.2.1
    · simpa only [SimpleGraph.mem_neighborFinset] using hx.2.2.2.1
    · simpa only [SimpleGraph.mem_neighborFinset] using hx.2.2.2.2.1
  exact (hfour u u' a b c c).trans (by exact_mod_cast Finset.card_le_card hinc)

/-- Construct triangular paired-absorber profiles from the four-root
    hypotheses and the original supplied cycle coefficients. -/
def ordinary_triangle_profiles_from_four_neighbourhoods
    (Q F:SimpleGraph V) (H:V→U→Prop) (β b B η L:ℝ) (hβ:0<β) (hL:0≤L)
    (hF:∀ v,(F.degree v:ℝ)≤L)
    (hfour:∀ u u' a b c d,β*Fintype.card V≤
      ((Finset.univ.filter (fun x=>H x u∧H x u'∧Q.Adj a x∧Q.Adj b x∧Q.Adj c x∧Q.Adj d x)).card:ℝ))
    (hbudget:(2+3:ℝ)*(L+1)≤β/2*Fintype.card V)
    (hnb:2*(2+1:ℝ)^2≤ordinaryLocalCountCoeff 2 β*Fintype.card V)
    (hnp:2*(2:ℝ)*(2*(2+1)+(2+1)*2)≤ordinaryLocalCountCoeff 2 β*Fintype.card V)
    (w:∀ u u':U,u≠u'→LocalOrdinaryCycle Q F (Finset.univ.filter (fun v=>H v u∧H v u')) 3→ℝ)
    (hw:∀ u u' (hne:u≠u') C,b/(Fintype.card V:ℝ)^2≤w u u' hne C ∧
      w u u' hne C≤B/(Fintype.card V:ℝ)^2)
    (hdeg:∀ u u' (hne:u≠u'),∀ v∈Finset.univ.filter (fun v=>H v u∧H v u'),
      |1-hypergraphWeightedDegree localOrdinaryVertices (w u u' hne) v|≤η) :
    OrdinaryCommonCycleProfiles Q F H 3 (fun (_:Unit)=>pairedAbsorberTemplate 3) β
      ((ordinaryLocalCountCoeff 2 β/2)^4) b B η := by
  let v:V:=Classical.arbitrary V
  have hsize:∀ u u':U,u≠u'→β*Fintype.card V≤
      ((Finset.univ.filter (fun x=>H x u∧H x u')).card:ℝ):=by
    intro u u' _
    exact (hfour u u' v v v v).trans (by
      exact_mod_cast Finset.card_le_card (by intro x hx; simp only [Finset.mem_filter,Finset.mem_univ,true_and] at *;exact ⟨hx.1,hx.2.1⟩))
  have hcommon:∀ u u':U,u≠u'→∀ S:Finset V,S.card≤(if 2=2 then 3 else 2)→
      β*Fintype.card V≤((common (Finset.univ.filter (fun x=>H x u∧H x u')) S
        (fun x=>Q.neighborFinset x)).card:ℝ):=by
    intro u u' _ S hS
    exact ordinary_triangle_common_geometry Q H β hfour u u' S (by simpa using hS)
  exact ordinary_common_profiles_from_geometry 2 (by omega) Q F H β b B η β L hβ hL hF
    hsize hcommon hbudget hnb hnp w hw hdeg

end Oberwolfach
