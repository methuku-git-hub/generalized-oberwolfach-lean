module

public import Oberwolfach.ColourRetentionCoins
public import Oberwolfach.MonochromaticWitnessCertificates

@[expose] public section

/-! Concrete witnesses for colours assigned in a vertex set and colours
rejected there after the tentative-colouring round. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def colourAssignedIn {V C : Type*} (Q : Finset V) (σ : V → C×Bool) (c : C) : Prop :=
  ∃ v∈Q,(σ v).1=c

def colourRejectedIn {V C : Type*} (G : SimpleGraph V)
    (Q : Finset V) (σ : V → C×Bool) (c : C) : Prop :=
  ∃ v∈Q,(σ v).1=c ∧ ¬coinColourSurvives G σ v

theorem colourAssignedIn_witness {V C : Type*}
    (Q : Finset V) (σ : V → C×Bool) (c : C) (h : colourAssignedIn Q σ c) :
    ∃ W : Finset V,W.card≤1 ∧ (∀ i∈W,(σ i).1=c) ∧
      ∀ τ,(∀ i∈W,σ i=τ i) → colourAssignedIn Q τ c := by
  classical
  obtain ⟨v,hv,hc⟩ := h
  refine ⟨{v},by simp,?_,?_⟩
  · intro i hi
    simpa only [Finset.mem_singleton.mp hi] using hc
  · intro τ he
    exact ⟨v,hv,(congrArg Prod.fst (he v (Finset.mem_singleton_self _))).symm.trans hc⟩

theorem colourRejectedIn_witness {V C : Type*}
    (G : SimpleGraph V) (Q : Finset V) (σ : V → C×Bool) (c : C)
    (h : colourRejectedIn G Q σ c) :
    ∃ W : Finset V,W.card≤2 ∧ (∀ i∈W,(σ i).1=c) ∧
      ∀ τ,(∀ i∈W,σ i=τ i) → colourRejectedIn G Q τ c := by
  classical
  obtain ⟨v,hv,hc,hbad⟩ := h
  by_cases hcoin : (σ v).2=true
  · have hex : ∃ u,G.Adj v u ∧ (σ u).1=(σ v).1 := by
      by_contra hn
      apply hbad
      refine ⟨hcoin,?_⟩
      intro u hu he
      exact hn ⟨u,hu,he⟩
    obtain ⟨u,hu,huc⟩ := hex
    refine ⟨{v,u},by simpa using Finset.card_insert_le v ({u} : Finset V),?_,?_⟩
    · intro i hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with hi|hi
      · simpa only [hi] using hc
      · simpa only [hi] using huc.trans hc
    · intro τ he
      have hvτ := he v (Finset.mem_insert_self _ _)
      have huτ := he u (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      refine ⟨v,hv,(congrArg Prod.fst hvτ).symm.trans hc,?_⟩
      intro hkeep
      exact hkeep.2 u hu ((congrArg Prod.fst huτ).symm.trans
        (huc.trans (congrArg Prod.fst hvτ)))
  · refine ⟨{v},by simp,?_,?_⟩
    · intro i hi
      simpa only [Finset.mem_singleton.mp hi] using hc
    · intro τ he
      have hvτ := he v (Finset.mem_singleton_self _)
      refine ⟨v,hv,(congrArg Prod.fst hvτ).symm.trans hc,?_⟩
      intro hkeep
      exact hcoin ((congrArg Prod.snd hvτ).trans hkeep.1)

theorem witnessed_count_threshold
    {I J Ω C : Type*} [Fintype J] [DecidableEq I]
    (P : J → (I → Ω) → Prop) (Q : Finset J) (colour : Ω → C)
    (x : I → Ω) (c : C) {k a : ℕ}
    (h : ∀ j∈Q,P j x →
      ∃ W : Finset I,W.card≤k ∧ (∀ i∈W,colour (x i)=c) ∧
        ∀ y,(∀ i∈W,x i=y i) → P j y)
    (ha : a≤(Q.filter (fun j=>P j x)).card) :
    ∃ W : Finset I,W.card≤k*Q.card ∧ (∀ i∈W,colour (x i)=c) ∧
      ∀ y,(∀ i∈W,x i=y i) → a≤(Q.filter (fun j=>P j y)).card := by
  classical
  let T := Q.filter (fun j=>P j x)
  let W : J → Finset I := fun j=>
    if hj : j∈T then Classical.choose (h j (Finset.mem_filter.mp hj).1
      (Finset.mem_filter.mp hj).2) else ∅
  have hW (j : J) (hj : j∈T) :
      (W j).card≤k ∧ (∀ i∈W j,colour (x i)=c) ∧
        ∀ y,(∀ i∈W j,x i=y i) → P j y := by
    dsimp only [W]
    rw [dif_pos hj]
    exact Classical.choose_spec (h j (Finset.mem_filter.mp hj).1
      (Finset.mem_filter.mp hj).2)
  refine ⟨T.biUnion W,?_,?_,?_⟩
  · calc
      _ ≤ ∑ j∈T,(W j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j∈T,k := Finset.sum_le_sum (fun j hj=>(hW j hj).1)
      _ = k*T.card := by simp [mul_comm]
      _ ≤ k*Q.card := Nat.mul_le_mul_left _ (Finset.card_le_card (Finset.filter_subset _ _))
  · intro i hi
    obtain ⟨j,hj,hi⟩ := Finset.mem_biUnion.mp hi
    exact (hW j hj).2.1 i hi
  · intro y he
    apply ha.trans
    apply Finset.card_le_card
    intro j hj
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,?_⟩
    exact (hW j hj).2.2 y (fun i hi=>he i (Finset.mem_biUnion.mpr ⟨j,hj,hi⟩))

end Oberwolfach
