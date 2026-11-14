module

public import Oberwolfach.RetainedMarkedSpokeChanges
public import Oberwolfach.FiniteConjunctionChanges
public import Oberwolfach.MarkedRowCommonEvent
public import Oberwolfach.MarkedIndexCommonEvent

@[expose] public section

/-! Deterministic row and index stability for the actual retained labels.
All physical rim states, admissible domains and comparison targets remain
fixed. The error is charged at the original outer-domain scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def retainedMarkedRowCount (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (g₀ : Γ) (t : ℕ)
    (K : StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g₀) t)
    (C : Finset V) (S : Finset (Bool×Bool×V)) (J : Finset (Bool×U)) (g : Γ) (j : Color) : ℝ :=
  ∑ x∈C,if (∀ a∈S,rawMarkedPairRims P π d σ (markedRowRim a x)) ∧
    (∀ a∈J,retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g₀ t K g j a.1 x a.2) then 1 else 0

def retainedMarkedIndexCount (π : Equiv.Perm V) (d : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (g₀ : Γ) (t : ℕ)
    (K : StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g₀) t)
    (B : Finset U) (J : Finset (Bool×V)) (g : Γ) (j : Color) : ℝ :=
  ∑ u∈B,if ∀ a∈J,retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g₀ t K g j a.1 a.2 u then 1 else 0

theorem retainedMarkedRowCount_change (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (g₀ : Γ) (t : ℕ)
    (K : StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g₀) t)
    (A C : Finset V) (hCA : C⊆A) (S : Finset (Bool×Bool×V)) (J : Finset (Bool×U))
    (g : Γ) (j : Color) (δ : ℝ)
    (hδ : ∀ u,((A.filter (fun x=>retainedRawFamilyState π d (fun e=>σ (Sum.inr e)) g₀ t K (x,u)≠
      rawIntervalFamilyState π d (fun e=>σ (Sum.inr e)) (x,u))).card:ℝ)≤δ) :
    |retainedMarkedRowCount P π d σ g₀ t K C S J g j-rawMarkedRowCount P π d C S J g j σ|≤J.card*δ := by
  have hh := finiteConjunction_sum_change_at_outer A C hCA J
    (fun x=>∀ a∈S,rawMarkedPairRims P π d σ (markedRowRim a x))
    (fun a x=>rawMarkedPairSpokes π d σ g j a.1 x a.2)
    (fun a x=>retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g₀ t K g j a.1 x a.2) δ (by
      intro a ha
      have hc := (retainedMarkedSpokes_col_changes π d (fun e=>σ (Sum.inr e)) g₀ t K g j a.1 a.2 A).trans (hδ a.2)
      convert hc using 1
      apply Finset.sum_congr rfl
      intro x hx
      dsimp only [bipAdj,rawMarkedPairSpokes]
      split_ifs <;> rfl)
  convert hh using 1
  apply congrArg abs
  apply congrArg₂ (fun x y : ℝ=>x-y)
  · unfold retainedMarkedRowCount
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs <;> rfl
  · unfold rawMarkedRowCount
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs <;> rfl

theorem retainedMarkedIndexCount_change (π : Equiv.Perm V) (d : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (g₀ : Γ) (t : ℕ)
    (K : StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g₀) t)
    (B : Finset U) (J : Finset (Bool×V)) (g : Γ) (j : Color) (δ : ℝ)
    (hδ : ∀ x,((B.filter (fun u=>retainedRawFamilyState π d (fun e=>σ (Sum.inr e)) g₀ t K (x,u)≠
      rawIntervalFamilyState π d (fun e=>σ (Sum.inr e)) (x,u))).card:ℝ)≤δ) :
    |retainedMarkedIndexCount π d σ g₀ t K B J g j-rawMarkedIndexCount π d B J g j σ|≤J.card*δ := by
  have hh := finiteConjunction_sum_change_at_outer B B (fun _ h=>h) J (fun _=>True)
    (fun a u=>rawMarkedPairSpokes π d σ g j a.1 a.2 u)
    (fun a u=>retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g₀ t K g j a.1 a.2 u) δ (by
      intro a ha
      have hc := (retainedMarkedSpokes_row_changes π d (fun e=>σ (Sum.inr e)) g₀ t K g j a.1 a.2 B).trans (hδ a.2)
      convert hc using 1
      apply Finset.sum_congr rfl
      intro u hu
      dsimp only [bipAdj,rawMarkedPairSpokes]
      split_ifs <;> rfl)
  simpa only [true_and,retainedMarkedIndexCount,rawMarkedIndexCount] using hh

end Oberwolfach
