module

public import Oberwolfach.FixedSizeProfileConditioning
public import Oberwolfach.ProfileRestrictionCounts

@[expose] public section

/-! Fixed root labels that have to lie in a sample outside F. Membership
in the sampled ground set is exactly the stated conditioning event;
labels forbidden outside Z cannot become eligible in any outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

def profileRequiredRoots (F Z X : Finset (Σ i,V i)) (i : I) : Finset (ProfileRemainingClass F i) :=
  Finset.univ.filter (fun v => (⟨i,v.val⟩ : Σ i,V i)∈X ∧ (⟨i,v.val⟩ : Σ i,V i)∉Z)

theorem profileRequiredRoots_map_subset (F Z X : Finset (Σ i,V i)) :
    (Finset.univ.sigma (profileRequiredRoots F Z X)).map (profileComplementEmbedding F)⊆X := by
  intro x hx
  obtain ⟨⟨i,v⟩,hv,rfl⟩ := Finset.mem_map.mp hx
  exact (Finset.mem_filter.mp (Finset.mem_sigma.mp hv).2).2.1

theorem profileRequiredRoots_card (F Z X : Finset (Σ i,V i)) (i : I) :
    (profileRequiredRoots F Z X i).card≤X.card := by
  have hs := Finset.card_le_card (profileRequiredRoots_map_subset F Z X)
  rw [Finset.card_map,Finset.card_sigma] at hs
  exact (Finset.single_le_sum (s:=Finset.univ) (f:=fun j => (profileRequiredRoots F Z X j).card)
    (fun j _ => Nat.zero_le _) (Finset.mem_univ i)).trans hs

theorem profileRequiredRoots_eligibility (F Z X : Finset (Σ i,V i))
    (hcompat : X∩F⊆Z) (m : I → ℕ) (σ : ∀ i,FixedSubset (ProfileRemainingClass F i) (m i)) :
    X⊆(profileRootSet σ).map (profileComplementEmbedding F)∪Z ↔
      ∀ i,profileRequiredRoots F Z X i⊆(σ i).val := by
  constructor
  · intro h i v hv
    obtain ⟨hvX,hvZ⟩ := (Finset.mem_filter.mp hv).2
    have hvS := (Finset.mem_union.mp (h hvX)).resolve_right hvZ
    have hvσ : (⟨i,v⟩ : Σ j,ProfileRemainingClass F j)∈profileRootSet σ := by
      obtain ⟨u,hu,he⟩ := Finset.mem_map.mp hvS
      have he' : u=(⟨i,v⟩ : Σ j,ProfileRemainingClass F j) := (profileComplementEmbedding F).injective he
      simpa only [he'] using hu
    exact (profileRootSet_mem σ i v).mp hvσ
  · intro h x hx
    by_cases hz : x∈Z
    · exact Finset.mem_union_right _ hz
    · have hf : x∉F := fun hf => hz (hcompat (Finset.mem_inter.mpr ⟨hx,hf⟩))
      obtain ⟨u,hu⟩ := (profileComplementEmbedding_range F x).mpr hf
      rcases u with ⟨i,v⟩
      have hv : v∈profileRequiredRoots F Z X i := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _,by change profileComplementEmbedding F ⟨i,v⟩∈X ∧ profileComplementEmbedding F ⟨i,v⟩∉Z;simpa only [hu] using And.intro hx hz⟩
      exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨⟨i,v⟩,(profileRootSet_mem σ i v).mpr (h i hv),hu⟩)

theorem profile_eligible_root_compatible (F Z X : Finset (Σ i,V i))
    (m : I → ℕ) (σ : ∀ i,FixedSubset (ProfileRemainingClass F i) (m i))
    (h : X⊆(profileRootSet σ).map (profileComplementEmbedding F)∪Z) : X∩F⊆Z := by
  intro x hx
  obtain ⟨hxX,hxF⟩ := Finset.mem_inter.mp hx
  rcases Finset.mem_union.mp (h hxX) with hs|hz
  · obtain ⟨u,_,hu⟩ := Finset.mem_map.mp hs
    exact False.elim ((profileComplementEmbedding_range F x).mp ⟨u,hu⟩ hxF)
  · exact hz

theorem profile_conditioned_sample_feasible (a : I → ℕ) (ha : ∀ i,1≤a i)
    (c t : ℕ) (ht : c≤t) (F : Finset (Σ i,V i))
    (T : ∀ i,Finset (ProfileRemainingClass F i)) (hT : ∀ i,(T i).card≤c)
    (hm : ∀ i,a i*t≤Fintype.card (ProfileRemainingClass F i)) :
    (∀ i,(T i).card≤a i*t) ∧
    (∀ i,a i*t-(T i).card≤Fintype.card {v : ProfileRemainingClass F i // v∉T i}) := by
  constructor
  · intro i
    exact (hT i).trans (ht.trans (by simpa only [one_mul] using Nat.mul_le_mul_right t (ha i)))
  · intro i
    rw [Fintype.card_subtype_compl,Fintype.card_coe]
    exact Nat.sub_le_sub_right (hm i) _

theorem profile_conditioned_sample_steps (a : I → ℕ) (c t : ℕ) (hs : ∑ i,a i=c)
    (F : Finset (Σ i,V i)) (T : ∀ i,Finset (ProfileRemainingClass F i)) :
    ∑ i,((a i*t-(T i).card:ℕ):ℝ)≤(c:ℝ)*t := by
  have hh : ∑ i,(a i*t-(T i).card)≤c*t := by
    calc
      _ ≤ ∑ i,a i*t := Finset.sum_le_sum (fun i _ => Nat.sub_le _ _)
      _ = _ := by rw [← Finset.sum_mul,hs]
  exact_mod_cast hh

end Oberwolfach
