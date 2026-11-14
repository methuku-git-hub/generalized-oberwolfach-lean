module

public import Oberwolfach.RetainedMarkedSpokeChanges
public import Oberwolfach.RawMarkedPairRestriction

@[expose] public section

/-! Restricting a globally retained sample transports deterministic
change bounds. No assertion is made that the restricted retention choices
have the local uniform-retention law or a common local retained size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

variable (f : W↪oV) (g : Z↪U) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
  (hcomm : ∀ x,f (ρ x)=π (f x)) (d : ℕ) (σ : RawMarkedOutcome V U Γ Color)
  (g₀ : Γ) (t : ℕ)
  (K : StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g₀) t)
  (a : Γ) (j : Color)

include hcomm

theorem retainedMarked_restricted_col_changes (A : Finset W) (δ : ℝ)
    (hδ : ∀ u,(((A.image f).filter (fun x=>retainedRawFamilyState π d (fun e=>σ (Sum.inr e)) g₀ t K (x,u)≠
      rawIntervalFamilyState π d (fun e=>σ (Sum.inr e)) (x,u))).card:ℝ)≤δ) :
    ∀ b z,(∑ x∈A,if ¬(rawMarkedPairSpokes ρ d (rawMarkedRestrictPair f g σ) a j b x z ↔
      retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g₀ t K a j b (f x) (g z)) then (1:ℝ) else 0)≤δ := by
  intro b z
  have hh := (retainedMarkedSpokes_col_changes π d (fun e=>σ (Sum.inr e)) g₀ t K a j b (g z) (A.image f)).trans (hδ (g z))
  rw [Finset.sum_image (by intro x hx y hy he;exact f.injective he)] at hh
  apply le_trans (le_of_eq ?_) hh
  apply Finset.sum_congr rfl
  intro x hx
  have he := rawMarkedRestrictPair_spokes f g π ρ hcomm d σ a j b x z
  rw [he]
  simp only [bipAdj,rawMarkedPairSpokes]
  split_ifs <;> rfl

theorem retainedMarked_restricted_row_changes (B : Finset Z) (δ : ℝ)
    (hδ : ∀ x,(((B.image g).filter (fun u=>retainedRawFamilyState π d (fun e=>σ (Sum.inr e)) g₀ t K (x,u)≠
      rawIntervalFamilyState π d (fun e=>σ (Sum.inr e)) (x,u))).card:ℝ)≤δ) :
    ∀ b x,(∑ z∈B,if ¬(rawMarkedPairSpokes ρ d (rawMarkedRestrictPair f g σ) a j b x z ↔
      retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g₀ t K a j b (f x) (g z)) then (1:ℝ) else 0)≤δ := by
  intro b x
  have hh := (retainedMarkedSpokes_row_changes π d (fun e=>σ (Sum.inr e)) g₀ t K a j b (f x) (B.image g)).trans (hδ (f x))
  rw [Finset.sum_image (by intro z hz w hw he;exact g.injective he)] at hh
  apply le_trans (le_of_eq ?_) hh
  apply Finset.sum_congr rfl
  intro z hz
  have he := rawMarkedRestrictPair_spokes f g π ρ hcomm d σ a j b x z
  rw [he]
  simp only [bipAdj,rawMarkedPairSpokes]
  split_ifs <;> rfl

end Oberwolfach
