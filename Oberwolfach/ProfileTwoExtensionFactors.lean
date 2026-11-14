module

public import Oberwolfach.ProfileExtensionAvoidingPairs
public import Oberwolfach.ResourceFactorDisplayedPairs

@[expose] public section

/-! Both factors on the two different ground sets are constructed from
the same supplied weights and local absorber counts. Sampling these
inputs remains a separate probabilistic stage. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 256
set_option maxHeartbeats 4200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I T : Type} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype T] [DecidableEq T]

theorem profile_two_extension_factors_from_counts (a : I → ℕ) (c J : ℕ) (hc : 3 ≤ c)
    (ha : ∀ i,1 ≤ a i) (hsize : ∑ i,a i=c)
    (S : T → VertexAbsorberTemplate c) (a₀ b B : ℝ)
    (ha₀ : 0 < a₀) (hb : 0 < b) (hB : 0 ≤ B) :
    ∃ η : ℝ,0 < η ∧ ∀ q : ℕ,∃ t₀ : ℕ,∀ t z : ℕ,t₀ ≤ t → z ≤ q →
      ∀ (V : I → Type) [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
        (C : Type) [Fintype C] [DecidableEq C],
      ∀ (R : C → Finset (Σ i,V i)) (w : C → ℝ) (A Z : Finset (Σ i,V i)),
      Disjoint A Z →
      (∀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈A)).card=a i*t) →
      (∀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈Z)).card=a i*z) →
      (∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i) →
      (∀ U : Finset (Σ i,V i),Fintype.card {C₀ : C // R C₀=U} ≤ J) →
      (∀ C₀,b/(t+z:ℕ)^(c-1) ≤ w C₀ ∧ w C₀ ≤ B/(t+z:ℕ)^(c-1)) →
      (∀ v∈A∪Z,|1-hypergraphWeightedDegree R (inducedResourceWeight R w (insert v A)) v| ≤ η) →
      (∀ σ : ∀ i,FixedSubset (V i) (a i),profileRootSet σ⊆A∪Z →
        a₀*(t+z:ℕ)^(c*c) ≤ absorberGroundCount R S (profileRootSet σ) A) →
      ∀ F : C → Finset ((Σ i,V i)×(Σ i,V i)),
      (∀ C₀,∀ e∈F C₀,e.1≠e.2 ∧ e.1∈R C₀ ∧ e.2∈R C₀) →
      (∀ C₀,(F C₀).card ≤ c) →
      (∀ C₀ v,((F C₀).filter (fun e => v=e.1 ∨ v=e.2)).card ≤ 2) →
      ∃ D₀ D₁ : Finset C,
        ((∀ x∈D₀,∀ y∈D₀,x≠y → Disjoint (R x) (R y)) ∧ D₀.biUnion R=A) ∧
        ((∀ x∈D₁,∀ y∈D₁,x≠y → Disjoint (R x) (R y)) ∧ D₁.biUnion R=A∪Z) ∧
        Disjoint (D₀.biUnion F) (D₁.biUnion F) ∧
        ∀ C₀∈D₁,(R C₀∩Z).card ≤ 1 := by
  obtain ⟨η₀,hη₀,k₀,hfactor₀⟩ := profile_factor_on_subset a c J hc ha hsize S a₀
    (b/(2:ℝ)^(c-1)) B ha₀ (by positivity) hB
  obtain ⟨η₁,hη₁,hfactor₁⟩ := profile_extension_avoiding_pairs a c J hc ha hsize S a₀ b B ha₀ hb hB
  refine ⟨min η₀ η₁,lt_min hη₀ hη₁,?_⟩
  intro q
  obtain ⟨k₁,hfactor₁⟩ := hfactor₁ (c*q) 2
  refine ⟨max (max k₀ k₁) (max q 1),?_⟩
  intro t z ht hz V _ _ C _ _ R w A Z hAZ hA hZ hR hJ hw herr habs F hF hFsize hFdeg
  have ht₀ : k₀ ≤ t := (le_max_left _ _).trans ((le_max_left _ _).trans ht)
  have ht₁ : k₁ ≤ t := (le_max_right _ _).trans ((le_max_left _ _).trans ht)
  have htq : q ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have ht1 : 1 ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have htpos : (0:ℝ)<t := by exact_mod_cast (show 0<t by omega)
  have hkt : (t:ℝ) ≤ (t+z:ℕ) := by exact_mod_cast (Nat.le_add_right t z)
  have hkpos : (0:ℝ)<(t+z:ℕ) := htpos.trans_le hkt
  have hk2t : ((t+z:ℕ):ℝ) ≤ 2*t := by exact_mod_cast (show t+z ≤ 2*t by omega)
  have hw₀ (C₀) : (b/(2:ℝ)^(c-1))/(t:ℝ)^(c-1) ≤ w C₀ ∧ w C₀ ≤ B/(t:ℝ)^(c-1) := by
    constructor
    · calc
        _ = b/((2:ℝ)*t)^(c-1) := by rw [mul_pow];field_simp
        _ ≤ b/(t+z:ℕ)^(c-1) := div_le_div_of_nonneg_left hb.le (pow_pos hkpos _)
          (pow_le_pow_left₀ hkpos.le hk2t _)
        _ ≤ _ := (hw C₀).1
    · exact (hw C₀).2.trans (div_le_div_of_nonneg_left hB (pow_pos htpos _)
        (pow_le_pow_left₀ htpos.le hkt _))
  have herr₀ (v) (hv : v∈A) : |1-hypergraphWeightedDegree R (inducedResourceWeight R w A) v| ≤ η₀ := by
    have hh := (herr v (Finset.mem_union_left _ hv)).trans (min_le_left η₀ η₁)
    simpa only [Finset.insert_eq_of_mem hv] using hh
  have habs₀ (σ : ∀ i,FixedSubset (V i) (a i)) (hσ : profileRootSet σ⊆A) :
      a₀*(t:ℝ)^(c*c) ≤ absorberGroundCount R S (profileRootSet σ) A := by
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htpos.le hkt _) ha₀.le).trans
      (habs σ (hσ.trans Finset.subset_union_left))
  obtain ⟨D₀,hD₀,hcover₀⟩ := hfactor₀ t ht₀ V C R w A hA hR hJ hw₀ herr₀ habs₀
  let E := D₀.biUnion F
  have hRC (C₀ : C) : (R C₀).card=c := by rw [sigma_finset_card];simp only [hR];exact hsize
  have hEsize : E.card ≤ A.card := by
    rw [← hcover₀]
    exact resource_factor_pairs_card R F D₀ hD₀ (fun C₀ _ => by rw [hRC];exact hFsize C₀)
  have hEd (v) : (E.filter (fun e => v=e.1 ∨ v=e.2)).card ≤ 2 :=
    resource_factor_pairs_incidence R F D₀ hD₀ (fun C₀ _ e he => (hF C₀ e he).2) 2
      (fun C₀ _ v => hFdeg C₀ v) v
  have hE : ∀ e∈E,e.1≠e.2 := by
    intro e he
    obtain ⟨C₀,_,he⟩ := Finset.mem_biUnion.mp he
    exact (hF C₀ e he).1
  have hZsize : Z.card ≤ c*q := by
    rw [sigma_finset_card]
    simp only [hZ,← Finset.sum_mul,hsize]
    exact Nat.mul_le_mul_left c hz
  have hY (i) : (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈A∪Z)).card=a i*(t+z) := by
    have he : Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈A∪Z)=
        (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈A))∪
        (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈Z)) := by ext v;simp
    rw [he,Finset.card_union_of_disjoint,hA,hZ,Nat.mul_add]
    apply Finset.disjoint_left.mpr
    intro v hvA hvZ
    exact Finset.disjoint_left.mp hAZ (Finset.mem_filter.mp hvA).2 (Finset.mem_filter.mp hvZ).2
  obtain ⟨D₁,hD₁,hcap,havoid⟩ := hfactor₁ (t+z) (ht₁.trans (Nat.le_add_right t z)) V C R w A Z hAZ hZsize hY
    hR hJ hw (fun v hv => (herr v hv).trans (min_le_right η₀ η₁)) habs E hE hEsize hEd
  refine ⟨D₀,D₁,⟨hD₀,hcover₀⟩,hD₁,?_,hcap⟩
  exact resource_pair_avoidance_disjoint R F D₁ E (fun C₀ _ e he => (hF C₀ e he).2) havoid

end Oberwolfach
