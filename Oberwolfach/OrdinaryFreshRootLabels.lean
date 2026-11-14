module

public import Oberwolfach.SparsePathChoices

@[expose] public section

/-! Fresh old-label copies for the finite expansion graphs. The row
copies avoid only the bounded old-label neighbourhoods; a linear forbidden
row set is handled by the available set A itself. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem exists_separated_row_set (F : SimpleGraph V) (A W R : Finset V)
    (d : ℝ) (hd : 0≤d) (hF : ∀ v,(F.degree v:ℝ)≤d) (n : ℕ)
    (hbudget : W.card+((R.card:ℝ)+n)*(d+1)<A.card) :
    ∃ S:Finset V,S.card=n ∧ S⊆A ∧ Disjoint S W ∧ Disjoint S R ∧
      (∀ v∈S,∀ w∈S,¬F.Adj v w) ∧ (∀ v∈S,∀ w∈R,¬F.Adj v w) := by
  induction n with
  | zero => exact ⟨∅,rfl,Finset.empty_subset _,by simp,by simp,by simp,by simp⟩
  | succ n ih =>
    have hd1 : 0≤d+1 := by linarith
    obtain ⟨S,hSc,hSA,hSW,hSR,hSS,hSF⟩ := ih (by push_cast at hbudget;nlinarith only [hbudget,hd1])
    let Z := R∪S
    let D := W∪(Z∪Z.biUnion (fun z=>F.neighborFinset z))
    have hZ : (Z.card:ℝ)≤R.card+n := by
      exact_mod_cast (Finset.card_union_le R S).trans_eq (by rw [hSc])
    have hD : (D.card:ℝ)≤W.card+((R.card:ℝ)+n)*(d+1) := by
      have hn := forbidden_used_neighbours_card F Z d hF
      have hc : (D.card:ℝ)≤W.card+(Z∪Z.biUnion (fun z=>F.neighborFinset z)).card := by
        exact_mod_cast Finset.card_union_le W (Z∪Z.biUnion (fun z=>F.neighborFinset z))
      have hm := mul_le_mul_of_nonneg_right hZ hd1
      linarith only [hn,hc,hm]
    have hDA : D.card<A.card := by
      have hh : (D.card:ℝ)<A.card := by push_cast at hbudget;nlinarith only [hbudget,hD,hd1]
      exact_mod_cast hh
    obtain ⟨v,hvA,hvD⟩ := Finset.exists_mem_notMem_of_card_lt_card hDA
    have hout : v∉W ∧ v∉Z ∧ v∉Z.biUnion (fun z=>F.neighborFinset z) := by
      simpa only [D,Finset.mem_union,not_or] using hvD
    have hvS : v∉S := fun h=>hout.2.1 (Finset.mem_union_right _ h)
    have hvR : v∉R := fun h=>hout.2.1 (Finset.mem_union_left _ h)
    have hvF : ∀ w∈Z,¬F.Adj v w := by
      intro w hw he
      exact hout.2.2 (Finset.mem_biUnion.mpr ⟨w,hw,(F.mem_neighborFinset _ _).mpr he.symm⟩)
    refine ⟨insert v S,by simp [hvS,hSc],Finset.insert_subset hvA hSA,
      Finset.disjoint_insert_left.mpr ⟨hout.1,hSW⟩,
      Finset.disjoint_insert_left.mpr ⟨hvR,hSR⟩,?_,?_⟩
    · intro a ha b hb
      simp only [Finset.mem_insert] at ha hb
      rcases ha with rfl|ha <;> rcases hb with rfl|hb
      · exact fun h=>h.ne rfl
      · exact hvF b (Finset.mem_union_right _ hb)
      · exact fun h=>hvF a (Finset.mem_union_right _ ha) h.symm
      · exact hSS a ha b hb
    · intro a ha b hb
      rcases Finset.mem_insert.mp ha with rfl|ha
      · exact hvF b (Finset.mem_union_left _ hb)
      · exact hSF a ha b hb

theorem exists_separated_row_embedding (I : Type) [Fintype I]
    (F : SimpleGraph V) (A W R : Finset V) (d : ℝ) (hd : 0≤d)
    (hF : ∀ v,(F.degree v:ℝ)≤d)
    (hbudget : W.card+((R.card:ℝ)+Fintype.card I)*(d+1)<A.card) :
    ∃ f:I↪V,(∀ i,f i∈A ∧ f i∉W ∧ f i∉R) ∧
      (∀ i j,¬F.Adj (f i) (f j)) ∧ (∀ i v,v∈R→¬F.Adj (f i) v) := by
  obtain ⟨S,hS,hSA,hSW,hSR,hSS,hSF⟩ := exists_separated_row_set F A W R d hd hF _ hbudget
  let e : I≃S := Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using hS.symm)
  let f : I↪V := e.toEmbedding.trans (Function.Embedding.subtype _)
  exact ⟨f,(fun i=>⟨hSA (e i).property,fun h=>Finset.disjoint_left.mp hSW (e i).property h,
    fun h=>Finset.disjoint_left.mp hSR (e i).property h⟩),
    (fun i j=>hSS _ (e i).property _ (e j).property),fun i v hv=>hSF _ (e i).property v hv⟩

theorem exists_fresh_hub_embedding (I : Type) [Fintype I] (B : Finset U)
    (hB : B.card+Fintype.card I≤Fintype.card U) :
    ∃ f:I↪U,∀ i,f i∉B := by
  let S := (Finset.univ:Finset U)\B
  have hS : Fintype.card I≤Fintype.card S := by
    have hc : S.card+B.card=Fintype.card U := by
      simpa only [S,Finset.card_univ] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
    simpa only [Fintype.card_coe] using (show Fintype.card I≤S.card by omega)
  obtain ⟨f⟩ : Nonempty (I↪S) := Function.Embedding.nonempty_of_card_le hS
  exact ⟨f.trans (Function.Embedding.subtype _),fun i=>(Finset.mem_sdiff.mp (f i).property).2⟩

end Oberwolfach
