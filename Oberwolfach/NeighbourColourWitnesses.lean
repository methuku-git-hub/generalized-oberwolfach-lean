module

public import Oberwolfach.DirectColourWitnesses
public import Oberwolfach.BoundedConflictWitnesses
public import Oberwolfach.WitnessCompositionLoads

@[expose] public section

/-! Simultaneous witnesses for assignment/rejection counts associated
with different roots. Corroborating vertices are chosen together so that
their multiplicities are bounded. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem neighbour_colour_witnesses
    {V C J : Type*} [Fintype V] (G : SimpleGraph V) (U : Finset V)
    (Q : V → Finset J) (T : J → Finset V) {k d : ℕ}
    (hQ : ∀ v∈U,(Q v).card≤k)
    (hlocal : ∀ (w : V) (S : Finset V),(∀ v∈S,G.Adj w v) →
      (∀ u∈S,∀ v∈S,u≠v → ¬G.Adj u v) → S.card≤k)
    (hinc : ∀ w,(U.filter (fun v=>∃ j∈Q v,w∈T j)).card≤d)
    (σ : V → C×Bool) (c : C) :
    ∃ W : V → Finset V,
      (∀ v∈U,(W v).card≤3*k) ∧
      (∀ i,(U.filter (fun v=>i∈W v)).card≤(k+3)*d) ∧
      (∀ v∈U,∀ τ,(∀ i∈W v,σ i=τ i) →
        (assignedSetIndices (Q v) T σ c).card≤(assignedSetIndices (Q v) T τ c).card ∧
        (rejectedSetIndices G (Q v) T σ c).card≤(rejectedSetIndices G (Q v) T τ c).card) := by
  classical
  let A := fun v=>assignedDirectVertices (Q v) T σ c
  let B := fun v=>rejectedDirectVertices G (Q v) T σ c
  let D := U.biUnion B
  have hBD (v : V) (hv : v∈U) : B v⊆D :=
    fun i hi=>Finset.mem_biUnion.mpr ⟨v,hv,hi⟩
  have hDcolour (i : V) (hi : i∈D) : (σ i).1=c := by
    obtain ⟨v,_hv,hi⟩ := Finset.mem_biUnion.mp hi
    exact (rejectedDirectVertices_spec G (Q v) T σ c hi).1
  have hDbad (i : V) (hi : i∈D) : ¬coinColourSurvives G σ i := by
    obtain ⟨v,_hv,hi⟩ := Finset.mem_biUnion.mp hi
    exact (rejectedDirectVertices_spec G (Q v) T σ c hi).2.1
  obtain ⟨f,hf,hfload⟩ := bounded_monochromatic_conflict_witnesses
    G D σ c hlocal hDcolour hDbad
  let W := fun v=>(A v∪B v)∪(B v).image f
  have hdirect (w : V) : (U.filter (fun v=>w∈A v∪B v)).card≤d := by
    have hsub : U.filter (fun v=>w∈A v∪B v)⊆
        U.filter (fun v=>∃ j∈Q v,w∈T j) := by
      intro v hv
      obtain ⟨hvU,hw⟩ := Finset.mem_filter.mp hv
      refine Finset.mem_filter.mpr ⟨hvU,?_⟩
      rcases Finset.mem_union.mp hw with hw|hw
      · exact (assignedDirectVertices_spec (Q v) T σ c hw).2
      · exact (rejectedDirectVertices_spec G (Q v) T σ c hw).2.2
    exact (Finset.card_le_card hsub).trans (hinc w)
  have hBload (w : V) : (U.filter (fun v=>w∈B v)).card≤d :=
    (Finset.card_le_card (show U.filter (fun v=>w∈B v)⊆
      U.filter (fun v=>w∈A v∪B v) from fun v hv=>
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).1,
          Finset.mem_union_right _ (Finset.mem_filter.mp hv).2⟩)).trans (hdirect w)
  have himage (w : V) : (U.filter (fun v=>w∈(B v).image f)).card≤(k+2)*d :=
    finite_witness_image_load U D B f hBD hBload hfload w
  refine ⟨W,?_,?_,?_⟩
  · intro v hv
    have hA := (assignedDirectVertices_card (Q v) T σ c).trans (hQ v hv)
    have hB := (rejectedDirectVertices_card G (Q v) T σ c).trans (hQ v hv)
    have hu₁ := Finset.card_union_le (A v) (B v)
    have hu₂ := Finset.card_union_le (A v∪B v) ((B v).image f)
    have hi : ((B v).image f).card≤(B v).card := Finset.card_image_le
    change ((A v∪B v)∪(B v).image f).card≤_
    change (A v).card≤k at hA
    change (B v).card≤k at hB
    omega
  · intro i
    have hsub : U.filter (fun v=>i∈W v)⊆
        (U.filter (fun v=>i∈A v∪B v))∪(U.filter (fun v=>i∈(B v).image f)) := by
      intro v hv
      obtain ⟨hvU,hi⟩ := Finset.mem_filter.mp hv
      rcases Finset.mem_union.mp hi with hi|hi
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hvU,hi⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvU,hi⟩)
    have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have h₁ := hdirect i
    have h₂ := himage i
    nlinarith
  · intro v hv τ he
    have hAeq (i : V) (hi : i∈A v) : σ i=τ i :=
      he i (Finset.mem_union_left _ (Finset.mem_union_left _ hi))
    have hBeq (i : V) (hi : i∈B v) : σ i=τ i :=
      he i (Finset.mem_union_left _ (Finset.mem_union_right _ hi))
    have hBbad (i : V) (hi : i∈B v) : ¬coinColourSurvives G τ i := by
      have heq := hBeq i hi
      have hfEq : σ (f i)=τ (f i) :=
        he (f i) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩))
      obtain ⟨hcol,hcase⟩ := hf i (hBD v hv hi)
      intro hkeep
      rcases hcase with ⟨_hself,hcoin⟩|hadj
      · exact hcoin ((congrArg Prod.snd heq).trans hkeep.1)
      · apply hkeep.2 (f i) hadj
        exact (congrArg Prod.fst hfEq).symm.trans
          (hcol.trans ((hDcolour i (hBD v hv hi)).symm.trans (congrArg Prod.fst heq)))
    exact ⟨Finset.card_le_card (assignedDirectVertices_preserve (Q v) T σ τ c hAeq),
      Finset.card_le_card (rejectedDirectVertices_preserve G (Q v) T σ τ c hBeq hBbad)⟩

end Oberwolfach
