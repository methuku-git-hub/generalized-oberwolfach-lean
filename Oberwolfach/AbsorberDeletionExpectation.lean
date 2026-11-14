module

public import Oberwolfach.ProfileAvoidingCounts
public import Oberwolfach.RootedProfileExpectation
public import Oberwolfach.ProfileSupportExpectation
public import Oberwolfach.AbsorberProfileSampling

@[expose] public section

/-! Exact expected number of the original labelled absorbers after
sampling outside a fixed forbidden set. Only free labels are tested;
root labels and all indexed cycles remain part of the records. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
    {C T : Type*} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T] {c : ℕ}

theorem absorber_deletion_profile_expectation
    (R : C → Finset (Σ i,V i)) (S : T → VertexAbsorberTemplate c) (a : I → ℕ)
    (hR : ∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i)
    (X Z : Finset (Σ i,V i)) (m : I → ℕ)
    [∀ i,Nonempty (FixedSubset (ProfileRemainingClass Z i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (ProfileRemainingClass Z i)) :
    (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (ProfileRemainingClass Z i) (m i)))).expectation
      (fun σ => absorberGroundCount R S X ((profileRootSet σ).map (profileComplementEmbedding Z)))=
      (∏ i,((m i).choose (c*a i):ℝ)/(Fintype.card (ProfileRemainingClass Z i)).choose (c*a i))*
        Fintype.card {D : LabelledAbsorberFamily R S X // Disjoint (labelledAbsorberFree R (S D.1) X D.2) Z} := by
  let D := LabelledAbsorberFamily R S X
  let F := fun d : D => labelledAbsorberFree R (S d.1) X d.2
  let w := fun d : D => if Disjoint (F d) Z then (1:ℝ) else 0
  have hw (d : D) (hn : w d≠0) : Disjoint (F d) Z := by
    by_contra hd
    simp only [w,hd,ite_false,ne_eq,not_true_eq_false] at hn
  have hF : ∀ d : D,w d≠0 → F d⊆Finset.univ.map (profileComplementEmbedding Z) := by
    intro d hn v hv
    have hz : v∉Z := fun hz => Finset.disjoint_left.mp (hw d hn) hv hz
    obtain ⟨u,hu⟩ := (profileComplementEmbedding_range Z v).mpr hz
    exact Finset.mem_map.mpr ⟨u,Finset.mem_univ _,hu⟩
  have ha : ∀ d : D,w d≠0 → ∀ i,
      (Finset.univ.filter (fun u : ProfileRemainingClass Z i => profileComplementEmbedding Z ⟨i,u⟩∈F d)).card=c*a i := by
    intro d hn i
    exact (profile_avoiding_preimage_class_card (F d) Z (hw d hn) i).trans
      (labelled_absorber_free_class_card R (S d.1) X d.2 a hR i)
  have hex := embedded_profile_weighted_support_expectation (profileComplementEmbedding Z) F w
    (fun i => c*a i) m hF ha hm
  have hsum (σ : ∀ i,FixedSubset (ProfileRemainingClass Z i) (m i)) :
      absorberGroundCount R S X ((profileRootSet σ).map (profileComplementEmbedding Z))=
        ∑ d : D,if F d⊆(profileRootSet σ).map (profileComplementEmbedding Z) then w d else 0 := by
    unfold absorberGroundCount
    simp only [Fintype.card_subtype]
    rw [← Finset.sum_boole (fun d : D => F d⊆(profileRootSet σ).map (profileComplementEmbedding Z)) Finset.univ]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hs : F d⊆(profileRootSet σ).map (profileComplementEmbedding Z)
    · have hd : Disjoint (F d) Z := by
        apply Finset.disjoint_left.mpr
        intro v hv hz
        obtain ⟨u,_,hu⟩ := Finset.mem_map.mp (hs hv)
        exact ((profileComplementEmbedding_range Z v).mp ⟨u,hu⟩) hz
      simp only [hs,ite_true,w,hd]
    · simp only [hs,ite_false]
  have hwcard : (∑ d : D,w d)=(Fintype.card {d : D // Disjoint (F d) Z}:ℝ) := by
    simp only [w,Fintype.card_subtype,Finset.sum_boole]
  simp_rw [hsum]
  rw [hex,hwcard]

end Oberwolfach
