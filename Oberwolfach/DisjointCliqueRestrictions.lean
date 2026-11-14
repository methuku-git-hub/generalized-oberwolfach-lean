module

public import Oberwolfach.ColourRetentionCoins
public import Oberwolfach.CertificateConcentration

@[expose] public section

/-! Removing pair intersections from a finite family. The probability cost
is bounded by the actual one-vertex retention probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def disjointFamilyRestriction {J V : Type*} (S : Finset J) (T : J → Finset V)
    (j : J) : Finset V :=
  (T j).filter (fun v=>∀ i∈S,i≠j → v∉T i)

theorem disjointFamilyRestriction_subset {J V : Type*} (S : Finset J)
    (T : J → Finset V) (j : J) : disjointFamilyRestriction S T j⊆T j :=
  Finset.filter_subset _ _

theorem disjointFamilyRestriction_disjoint {J V : Type*}
    (S : Finset J) (T : J → Finset V) {i j : J} (hi : i∈S) (hij : i≠j) :
    Disjoint (disjointFamilyRestriction S T i) (disjointFamilyRestriction S T j) := by
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  exact (Finset.mem_filter.mp hvj).2 i hi hij (Finset.mem_filter.mp hvi).1

theorem disjointFamilyRestriction_loss {J V : Type*}
    (S : Finset J) (T : J → Finset V) (j : J) {B : ℕ}
    (hpair : ∀ i∈S,i≠j → (T j∩T i).card≤B) :
    ((T j)\disjointFamilyRestriction S T j).card≤S.card*B := by
  classical
  have hsub : (T j)\disjointFamilyRestriction S T j⊆
      (S.erase j).biUnion (fun i=>T j∩T i) := by
    intro v hv
    obtain ⟨hvT,hvn⟩ := Finset.mem_sdiff.mp hv
    have hn : ¬∀ i∈S,i≠j → v∉T i := by
      intro h
      exact hvn (Finset.mem_filter.mpr ⟨hvT,h⟩)
    push_neg at hn
    obtain ⟨i,hi,hij,hvi⟩ := hn
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_erase.mpr ⟨hij,hi⟩,
      Finset.mem_inter.mpr ⟨hvT,hvi⟩⟩
  calc
    _ ≤ ((S.erase j).biUnion (fun i=>T j∩T i)).card := Finset.card_le_card hsub
    _ ≤ (S.erase j).card*B := Finset.card_biUnion_le_card_mul _ _ _ (fun i hi=>
      hpair i (Finset.mem_erase.mp hi).2 (Finset.mem_erase.mp hi).1)
    _ ≤ _ := Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.erase_subset _ _))

theorem finiteLaw_clique_restriction_loss
    {V C J : Type*} [Fintype V] [Fintype C]
    (G : SimpleGraph V) (μ : FiniteLaw (V → C×Bool))
    (S : Finset J) (T T' : J → Finset V) (hsub : ∀ j∈S,T' j⊆T j) (c : C) :
    0≤μ.probability (fun σ=>∀ j∈S,∃ v∈T j,coinRetainedColour G σ v=some c)-
      μ.probability (fun σ=>∀ j∈S,∃ v∈T' j,coinRetainedColour G σ v=some c) ∧
    μ.probability (fun σ=>∀ j∈S,∃ v∈T j,coinRetainedColour G σ v=some c)-
      μ.probability (fun σ=>∀ j∈S,∃ v∈T' j,coinRetainedColour G σ v=some c)≤
      ∑ j∈S,∑ v∈T j\T' j,μ.probability (fun σ=>coinRetainedColour G σ v=some c) := by
  classical
  let P := fun σ : V → C×Bool=>∀ j∈S,∃ v∈T j,coinRetainedColour G σ v=some c
  let Q := fun σ : V → C×Bool=>∀ j∈S,∃ v∈T' j,coinRetainedColour G σ v=some c
  let B := fun σ : V → C×Bool=>∃ j∈S,∃ v∈T j\T' j,coinRetainedColour G σ v=some c
  have hQP : ∀ σ,Q σ → P σ := by
    intro σ h j hj
    obtain ⟨v,hv,hc⟩ := h j hj
    exact ⟨v,hsub j hj hv,hc⟩
  have hPQB : ∀ σ,P σ → Q σ ∨ B σ := by
    intro σ hp
    by_cases hq : Q σ
    · exact Or.inl hq
    · right
      change ¬∀ j∈S,∃ v∈T' j,coinRetainedColour G σ v=some c at hq
      push_neg at hq
      obtain ⟨j,hj,hn⟩ := hq
      obtain ⟨v,hv,hc⟩ := hp j hj
      exact ⟨j,hj,v,Finset.mem_sdiff.mpr ⟨hv,fun hv'=>hn v hv' hc⟩,hc⟩
  have hmono := finiteLaw_probability_mono μ Q P hQP
  have hsplit := (finiteLaw_probability_mono μ P (fun σ=>Q σ ∨ B σ) hPQB).trans
    (finiteLaw_probability_or_le μ Q B)
  have hB : μ.probability B≤∑ j∈S,∑ v∈T j\T' j,
      μ.probability (fun σ=>coinRetainedColour G σ v=some c) := by
    apply (finiteLaw_union_bound μ S
      (fun j σ=>∃ v∈T j\T' j,coinRetainedColour G σ v=some c)).trans
    exact Finset.sum_le_sum (fun j _=>finiteLaw_union_bound μ (T j\T' j)
      (fun v σ=>coinRetainedColour G σ v=some c))
  change 0≤μ.probability P-μ.probability Q ∧ μ.probability P-μ.probability Q≤_
  constructor <;> linarith

end Oberwolfach
