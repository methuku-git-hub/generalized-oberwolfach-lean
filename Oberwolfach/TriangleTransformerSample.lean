module

public import Oberwolfach.ExternalRootedDenseSets

@[expose] public section

/-! A bounded fresh vertex set with large neighbourhoods at every selected
vertex and every prescribed external root. The uniform-subset sampling
argument is inherited from `external_rooted_dense_sets`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_transformer_sample (z : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hβ1 : β≤1) (hρ : 0<ρ) :
    ∃ s₀ : ℕ,∀ s : ℕ,s₀≤s → ∃ N : ℕ,∀ (V : Type) [Fintype V] [DecidableEq V],
      N≤Fintype.card V → ∀ (G : SimpleGraph V) (A Z : Finset V),Z.card=z →
      ρ*Fintype.card V≤(A.card:ℝ) →
      (∀ v∈A∪Z,(3/4+β/2)*(A.card:ℝ)≤((G.neighborFinset v∩A).card:ℝ)) →
      ∃ S : Finset V,S.card=s ∧ S⊆A ∧ Disjoint S Z ∧
        (∀ v∈S∪Z,(3/4+β/8)*(s:ℝ)≤((G.neighborFinset v∩S).card:ℝ)) := by
  obtain ⟨K,hK⟩:=external_rooted_dense_sets z β ρ hβ hβ1 hρ
  obtain ⟨M,hM⟩:=exists_nat_gt ((8/β)*z)
  refine ⟨max K M,?_⟩
  intro s hs
  obtain ⟨c,hc,hcN⟩:=hK s ((le_max_left K M).trans hs)
  obtain ⟨N,hN⟩:=hcN 0 (le_refl _)
  refine ⟨max N 1,?_⟩
  intro V _ _ hn G A Z hZ hA hdeg
  have hcount:=hN V ((le_max_left N 1).trans hn) G ⊥ A Z hZ hA (3/4)
    (by norm_num) (by norm_num) hdeg (by simp) (by simp)
  have hnpos : 0<(Fintype.card V:ℝ) := by
    exact_mod_cast (le_max_right N 1).trans hn
  have hpos : 0<c*(Fintype.card V:ℝ)^s := by positivity
  have hcardpos := hpos.trans_le hcount
  have hcardNat : 0<Fintype.card {T : FixedSubset V (z+s) // Z⊆T.val ∧ T.val⊆A∪Z ∧
      (∀ v∈T.val,(3/4+β/4)*(z+s:ℝ)≤((G.neighborFinset v∩T.val).card:ℝ)) ∧
      (∀ x∈T.val,∀ y∈T.val,¬(⊥:SimpleGraph V).Adj x y)} := by exact_mod_cast hcardpos
  obtain ⟨T⟩:=Fintype.card_pos_iff.mp hcardNat
  let S:=T.val.val\Z
  have hScard : S.card=s := by
    dsimp [S]
    rw [Finset.card_sdiff_of_subset T.property.1,T.val.property,hZ]
    omega
  have hSZ : S∪Z=T.val.val := Finset.sdiff_union_of_subset T.property.1
  have hSA : S⊆A := by
    intro v hv
    have hh:=Finset.mem_sdiff.mp hv
    rcases Finset.mem_union.mp (T.property.2.1 hh.1) with h|h
    · exact h
    · exact (hh.2 h).elim
  refine ⟨S,hScard,hSA,Finset.sdiff_disjoint,?_⟩
  intro v hv
  have hT:=T.property.2.2.1 v (hSZ ▸ hv)
  have hsplit : G.neighborFinset v∩T.val.val⊆(G.neighborFinset v∩S)∪Z := by
    intro w hw
    have hwT:=(Finset.mem_inter.mp hw).2
    by_cases hwZ:w∈Z
    · exact Finset.mem_union_right _ hwZ
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hw).1,Finset.mem_sdiff.mpr ⟨hwT,hwZ⟩⟩)
  have hcard:=(Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
  rw [hZ] at hcard
  have hcardR : ((G.neighborFinset v∩T.val.val).card:ℝ)≤(G.neighborFinset v∩S).card+(z:ℝ) := by
    exact_mod_cast hcard
  have hMs : (M:ℝ)≤s := by exact_mod_cast (le_max_right K M).trans hs
  have hmargin:=mul_le_mul_of_nonneg_right (hM.le.trans hMs) (by positivity : (0:ℝ)≤β/8)
  have he : ((8/β)*(z:ℝ))*(β/8)=z := by field_simp
  rw [he] at hmargin
  have hnonneg : 0≤(3/4+β/4)*(z:ℝ) := by positivity
  nlinarith only [hT,hcardR,hmargin,hnonneg]

end Oberwolfach
