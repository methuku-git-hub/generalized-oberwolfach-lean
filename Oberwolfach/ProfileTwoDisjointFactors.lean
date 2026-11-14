module

public import Oberwolfach.ProfileFactorAvoidingPairs
public import Oberwolfach.ResourceFactorDisplayedPairs

@[expose] public section

/-! Two factors with disjoint displayed endpoint sets, obtained from
the original profile weights and labelled absorber abundance. The
forbidden pairs for the second factor are constructed from the first. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 256
set_option maxHeartbeats 4800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I T : Type} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype T] [DecidableEq T]

theorem profile_two_disjoint_factors (a : I → ℕ) (c J : ℕ) (hc : 3 ≤ c)
    (ha : ∀ i,1 ≤ a i) (hsize : ∑ i,a i=c)
    (S : T → VertexAbsorberTemplate c) (a₀ b B : ℝ)
    (ha₀ : 0 < a₀) (hb : 0 < b) (hB : 0 ≤ B) :
    ∃ η : ℝ,0 < η ∧ ∃ k₀ : ℕ,∀ k : ℕ,k₀ ≤ k →
      ∀ (V : I → Type) [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
        (C : Type) [Fintype C] [DecidableEq C],
      (∀ i,Fintype.card (V i)=a i*k) →
      ∀ (R : C → Finset (Σ i,V i)) (w : C → ℝ),
      (∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i) →
      (∀ Y : Finset (Σ i,V i),Fintype.card {C₀ : C // R C₀=Y} ≤ J) →
      (∀ C₀,b/(k:ℝ)^(c-1) ≤ w C₀ ∧ w C₀ ≤ B/(k:ℝ)^(c-1)) →
      (∀ v,|1-hypergraphWeightedDegree R w v| ≤ η) →
      (∀ σ : ∀ i,FixedSubset (V i) (a i),
        a₀*(k:ℝ)^(c*c) ≤ Fintype.card (LabelledAbsorberFamily R S (profileRootSet σ))) →
      ∀ F : C → Finset ((Σ i,V i)×(Σ i,V i)),
      (∀ C₀,∀ e∈F C₀,e.1≠e.2 ∧ e.1∈R C₀ ∧ e.2∈R C₀) →
      (∀ C₀,(F C₀).card ≤ c) →
      (∀ C₀ v,((F C₀).filter (fun e => v=e.1 ∨ v=e.2)).card ≤ 2) →
      ∃ D₀ D₁ : Finset C,
        ((∀ x∈D₀,∀ y∈D₀,x≠y → Disjoint (R x) (R y)) ∧ D₀.biUnion R=Finset.univ) ∧
        ((∀ x∈D₁,∀ y∈D₁,x≠y → Disjoint (R x) (R y)) ∧ D₁.biUnion R=Finset.univ) ∧
        Disjoint (D₀.biUnion F) (D₁.biUnion F) := by
  obtain ⟨η₀,hη₀,k₀,h₀⟩ := profile_factor_extraction a c J hc ha hsize S a₀ b B ha₀ hb hB
  obtain ⟨η₁,hη₁,h₁⟩ := profile_factor_avoiding_pairs a c J hc ha hsize S a₀ b B ha₀ hb hB
  obtain ⟨k₁,h₁⟩ := h₁ 2
  refine ⟨min η₀ η₁,lt_min hη₀ hη₁,max k₀ k₁,?_⟩
  intro k hk V _ _ C _ _ hn R w hR hJ hw herr habs F hF hFsize hFd
  have hk₀ := (le_max_left k₀ k₁).trans hk
  have hk₁ := (le_max_right k₀ k₁).trans hk
  have herr₀ (v) := (herr v).trans (min_le_left η₀ η₁)
  have herr₁ (v) := (herr v).trans (min_le_right η₀ η₁)
  obtain ⟨D₀,hD₀⟩ := h₀ k hk₀ V C hn R w hR hJ hw herr₀ habs
  let E := D₀.biUnion F
  have hE (e) (he : e∈E) : e.1≠e.2 := by
    obtain ⟨C₀,_,heC⟩ := Finset.mem_biUnion.mp he
    exact (hF C₀ e heC).1
  have hRC (C₀ : C) : (R C₀).card=c := by rw [sigma_finset_card];simp only [hR];exact hsize
  have hnall : Fintype.card (Σ i,V i)=c*k := by
    simp only [Fintype.card_sigma,hn,← Finset.sum_mul,hsize]
  have hEsize : E.card ≤ c*k := by
    have hh := resource_factor_pairs_card R F D₀ hD₀.1 (fun C₀ _ => by simpa only [hRC] using hFsize C₀)
    rw [hD₀.2,Finset.card_univ,hnall] at hh
    exact hh
  have hEd (v : Σ i,V i) : (E.filter (fun e => v=e.1 ∨ v=e.2)).card ≤ 2 :=
    resource_factor_pairs_incidence R F D₀ hD₀.1 (fun C₀ _ e he => (hF C₀ e he).2)
      2 (fun C₀ _ v => hFd C₀ v) v
  obtain ⟨D₁,hD₁,havoid⟩ := h₁ k hk₁ V C hn R w hR hJ hw herr₁ habs E hE hEsize hEd
  exact ⟨D₀,D₁,hD₀,hD₁,resource_pair_avoidance_disjoint R F D₁ E
    (fun C₀ _ e he => (hF C₀ e he).2) havoid⟩

end Oberwolfach
