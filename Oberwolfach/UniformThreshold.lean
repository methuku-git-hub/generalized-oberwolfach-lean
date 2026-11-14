module

public import Oberwolfach.ThresholdBounds
public import Mathlib.Tactic

@[expose] public section

/-! The finite-exception argument in the proof of Theorem 1.1.
This proves the reduction, CONDITIONAL on the fixed-set theorem and the
threshold estimates named explicitly below. It does not prove those inputs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem allowed_lengths_mono {n : ℕ} {F : SimpleGraph (Fin n)}
    {S T : Set ℕ} (hST : S ⊆ T) (hF : AllowedCycleLengths F S) :
    AllowedCycleLengths F T := by
  intro v
  exact hST (hF v)

/-- Enlarge the allowed set without changing the prescribed factors. -/
theorem decompositionAt_transfer {S T : Set ℕ} {α β : ℝ} {n : ℕ}
    (hST : S ⊆ T) (hdeg : allowedThreshold T + β ≤ allowedThreshold S + α)
    (hT : DecompositionAt T β n) : DecompositionAt S α n := by
  classical
  intro D hD hbound F hF G hG
  apply hT D hD (le_trans ?_ hbound) F ?_ G hG
  · exact mul_le_mul_of_nonneg_right hdeg (Nat.cast_nonneg n)
  · intro i
    exact ⟨(hF i).1, allowed_lengths_mono hST (hF i).2⟩

/-- A finite exceptional set and a common tail, chosen using only alpha. -/
def SmallThresholdTail : Prop :=
  ∀ α : ℝ, 0 < α → ∃ E : Finset ℕ, ∃ T : Set ℕ,
    T.Nonempty ∧ (∀ r ∈ E, 3 ≤ r) ∧ (∀ r ∈ T, 3 ≤ r) ∧
    (∀ r, 3 ≤ r → r ∉ E → r ∈ T) ∧
    (∀ r ∈ T, cycleThreshold r ≤ (1 / 2 : ℝ) + α / 2)

/-- The fixed-set theorem and the explicitly stated threshold estimates imply
uniformity of the order threshold over ALL allowed length sets. -/
theorem uniform_of_fixed_set
    (hfixed : FixedSetTheorem)
    (hlower : ∀ r : ℕ, 3 ≤ r → (1 / 2 : ℝ) ≤ cycleThreshold r)
    (hupper : ∀ r : ℕ, 3 ≤ r → cycleThreshold r ≤ 1)
    (htail : SmallThresholdTail) : MainTheorem := by
  classical
  intro α hα
  obtain ⟨E, T, hTne, hE, hT, hcover, hsmall⟩ := htail α hα
  have hhalf : 0 < α / 2 := by linarith
  have hf : ∀ B : {B : Finset ℕ // B ⊆ E},
      ∃ N : ℕ, ∀ n ≥ N, DecompositionAt (T ∪ (B.val : Set ℕ)) (α / 2) n := by
    intro B
    apply hfixed (T ∪ (B.val : Set ℕ))
    · exact hTne.mono Set.subset_union_left
    · intro r hr
      rcases hr with hr | hr
      · exact hT r hr
      · exact hE r (B.property hr)
    · exact hhalf
  choose bound hbound using hf
  let bs : Finset {B : Finset ℕ // B ⊆ E} := E.powerset.attach.map
    ⟨fun B => ⟨B.val, Finset.mem_powerset.mp B.property⟩, by
      intro B C h; apply Subtype.ext
      exact congrArg (fun z : {B : Finset ℕ // B ⊆ E} => z.val) h⟩
  let N := bs.sup bound
  refine ⟨N, ?_⟩
  intro S hSne hS n hn
  let B : {B : Finset ℕ // B ⊆ E} := ⟨E.filter (fun r => r ∈ S), Finset.filter_subset _ _⟩
  have hBmem : B ∈ bs := by
    apply Finset.mem_map.mpr
    refine ⟨⟨B.val, Finset.mem_powerset.mpr B.property⟩, by simp, ?_⟩
    rfl
  have hBN : bound B ≤ N := Finset.le_sup hBmem
  let Sstar := T ∪ (B.val : Set ℕ)
  have hSstar : S ⊆ Sstar := by
    intro r hr
    by_cases hrE : r ∈ E
    · exact Or.inr (Finset.mem_filter.mpr ⟨hrE, hr⟩)
    · exact Or.inl (hcover r (hS r hr) hrE)
  have hbdd : BddAbove (cycleThreshold '' S) := by
    refine ⟨1, ?_⟩
    rintro y ⟨r, hr, rfl⟩
    exact hupper r (hS r hr)
  have hle : ∀ r ∈ S, cycleThreshold r ≤ allowedThreshold S := by
    intro r hr
    exact le_csSup hbdd ⟨r, hr, rfl⟩
  have hbase : (1 / 2 : ℝ) ≤ allowedThreshold S := by
    obtain ⟨r, hr⟩ := hSne
    exact (hlower r (hS r hr)).trans (hle r hr)
  have hsup : allowedThreshold Sstar ≤ allowedThreshold S + α / 2 := by
    apply csSup_le (hTne.mono Set.subset_union_left |>.image cycleThreshold)
    rintro y ⟨r, hr, rfl⟩
    rcases hr with hr | hr
    · linarith [hsmall r hr]
    · have hrS : r ∈ S := (Finset.mem_filter.mp hr).2
      linarith [hle r hrS]
  apply decompositionAt_transfer hSstar (show allowedThreshold Sstar + α / 2 ≤
      allowedThreshold S + α by linarith)
  exact hbound B n (hBN.trans hn)

/-- A cofinite upper bound supplies the finite exceptional-set interface. -/
theorem smallThresholdTail_of_cofinite
    (ht : ∀ α : ℝ, 0 < α → ∃ R : ℕ, ∀ r ≥ R,
      cycleThreshold r ≤ (1 / 2 : ℝ) + α / 2) : SmallThresholdTail := by
  classical
  intro α hα
  obtain ⟨R, hR⟩ := ht α hα
  let E := (Finset.range R).filter (fun r => 3 ≤ r)
  let T : Set ℕ := {r | 3 ≤ r ∧ R ≤ r}
  refine ⟨E, T, ⟨max 3 R, le_max_left _ _, le_max_right _ _⟩, ?_, ?_, ?_, ?_⟩
  · intro r hr; exact (Finset.mem_filter.mp hr).2
  · intro r hr; exact hr.1
  · intro r hr hnot
    refine ⟨hr, ?_⟩
    by_contra hge
    have : r ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hr⟩
    exact hnot this
  · intro r hr; exact hR r hr.2

/-- The remaining nontrivial inputs are exposed, not installed as axioms. -/
theorem uniform_from_fixed_and_cofinite
    (hfixed : FixedSetTheorem)
    (hlower : ∀ r : ℕ, 3 ≤ r → (1 / 2 : ℝ) ≤ cycleThreshold r)
    (ht : ∀ α : ℝ, 0 < α → ∃ R : ℕ, ∀ r ≥ R,
      cycleThreshold r ≤ (1 / 2 : ℝ) + α / 2) : MainTheorem :=
  uniform_of_fixed_set hfixed hlower (fun r _ => cycleThreshold_le_one r)
    (smallThresholdTail_of_cofinite ht)

end Oberwolfach
