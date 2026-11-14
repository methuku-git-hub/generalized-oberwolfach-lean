module

public import Oberwolfach.ConfigurationReservoirOrder
public import Oberwolfach.UniversalAbsorberReservoir

@[expose] public section

/-! Constructing one small absorber reservoir before the uncovered set
is known. The finite configuration counts are the explicit inputs to
this selection step; their graph-specific derivation is separate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem small_universal_absorber (h c : ℕ) (K K' a L δ : ℝ)
    (hK : 0 < K) (hK' : 0 < K') (ha : 0 < a) (hL : 0 < L) (hδ : 0 < δ) :
    ∃ γ : ℝ,0 < γ ∧ ∃ n₀ : ℕ,∀ n : ℕ,n₀ ≤ n →
    ∀ (C I E W : Type*) [Fintype C] [Fintype I] [DecidableEq C] [DecidableEq I] [DecidableEq E] [DecidableEq W],
    ∀ (R : W → Finset E) (X : I → Finset E) (A : C → Finset E) (P : Finset (C×C)),
      (∀ z∈P,z.1≠z.2) →
      (∀ j k,j≠k → ¬Disjoint (A j) (A k) → (j,k)∈P) →
      (∀ j,(A j).card ≤ h+1) → (∀ j,HasResourceDecomposition R (A j)) →
      (Fintype.card C:ℝ) ≤ K*(n:ℝ)^(h+1) →
      (P.card:ℝ) ≤ K'*(n:ℝ)^(2*h+1) →
      (Fintype.card I:ℝ) ≤ L*(n:ℝ)^c →
      (∀ i,a*(n:ℝ)^(h+1) ≤
        ((Finset.univ.filter (fun j => HasResourceDecomposition R (A j∪X i))).card:ℝ)) →
    ∃ A₀ : Finset E,(A₀.card:ℝ) ≤ δ*n ∧ HasResourceDecomposition R A₀ ∧
      ∀ M : Finset I,(M.card:ℝ) ≤ γ*n →
        (∀ i∈M,∀ j∈M,i≠j → Disjoint (X i) (X j)) → Disjoint (M.biUnion X) A₀ →
        IsResourceAbsorber R (M.biUnion X) A₀ := by
  obtain ⟨γ,hγ,n₀,hn₀⟩ := configuration_reservoir_order h c K K' a L δ hK hK' ha hL hδ
  refine ⟨γ,hγ,n₀,?_⟩
  intro n hn C I E W _ _ _ _ _ _ R X A P hP hconflict hA hdec hC hPairs hI hchoices
  let T (i : I) := Finset.univ.filter (fun j => HasResourceDecomposition R (A j∪X i))
  obtain ⟨S,hS,hSS,hT⟩ := hn₀ n hn C I E A T P hP hconflict hA hC hPairs hI hchoices
  have hT' (i : I) : γ*n ≤ ((S.filter (fun j => HasResourceDecomposition R (A j∪X i))).card:ℝ) := by
    have he : S∩T i=S.filter (fun j => HasResourceDecomposition R (A j∪X i)) := by ext j;simp [T]
    simpa only [he] using hT i
  refine ⟨S.biUnion A,hS,resource_decomposition_biUnion R A S
    (fun j _ => hdec j) hSS,?_⟩
  exact universal_absorber_reservoir R X A S (γ*n) hSS (fun j _ => hdec j) hT'

end Oberwolfach
