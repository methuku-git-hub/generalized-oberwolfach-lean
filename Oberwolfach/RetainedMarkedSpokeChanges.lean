module

public import Oberwolfach.RawMarkedRetention
public import Oberwolfach.BipartiteIntersectionEstimates

@[expose] public section

/-! A changed spoke implies a changed pair label. This includes newly
exposed ordinary labels as well as removed marked labels. Every bound
uses the original row or index domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem labelIndicator_change_sum {X L : Type*} (A : Finset X) (f f' : X→L) (a : L) :
    (∑ x∈A,if ¬(f x=a ↔ f' x=a) then (1:ℝ) else 0)≤
      (A.filter (fun x=>f' x≠f x)).card := by
  simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.sum_le_sum
  intro x hx
  by_cases he : f' x=f x
  · simp [he]
  · split_ifs <;> norm_num

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def retainedRawMarkedSpokes (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (g₀ : Γ) (t : ℕ)
    (J : StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (g : Γ) (j : Color) : Bool→V→U→Prop
  | false,v,u=>retainedRawFamilyState π d σ g₀ t J (v,u)=some (Sum.inr j)
  | true,v,u=>retainedRawFamilyState π d σ g₀ t J (v,u)=some (Sum.inl g)

theorem retainedMarkedSpokes_row_changes (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (g₀ : Γ) (t : ℕ)
    (J : StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (g : Γ) (j : Color)
    (a : Bool) (v : V) (T : Finset U) :
    (∑ u∈T,bipAdj (fun x u=>¬(rawMarkedSpokes π d σ g j a x u ↔
      retainedRawMarkedSpokes π d σ g₀ t J g j a x u)) v u)≤
      ((T.filter (fun u=>retainedRawFamilyState π d σ g₀ t J (v,u)≠
        rawIntervalFamilyState π d σ (v,u))).card:ℝ) := by
  have hh := labelIndicator_change_sum T (fun u=>rawIntervalFamilyState π d σ (v,u))
    (fun u=>retainedRawFamilyState π d σ g₀ t J (v,u))
    (if a then some (Sum.inl g) else some (Sum.inr j))
  convert hh using 1
  · apply Finset.sum_congr rfl
    intro u hu
    cases a <;> simp only [bipAdj,rawMarkedSpokes,retainedRawMarkedSpokes,Bool.false_eq_true,ite_false,ite_true] <;> split_ifs <;> rfl
  · apply congrArg (fun n : ℕ=>(n:ℝ))
    apply congrArg Finset.card
    ext u
    simp only [Finset.mem_filter]

theorem retainedMarkedSpokes_col_changes (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (g₀ : Γ) (t : ℕ)
    (J : StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (g : Γ) (j : Color)
    (a : Bool) (u : U) (S : Finset V) :
    (∑ v∈S,bipAdj (fun x u=>¬(rawMarkedSpokes π d σ g j a x u ↔
      retainedRawMarkedSpokes π d σ g₀ t J g j a x u)) v u)≤
      ((S.filter (fun v=>retainedRawFamilyState π d σ g₀ t J (v,u)≠
        rawIntervalFamilyState π d σ (v,u))).card:ℝ) := by
  have hh := labelIndicator_change_sum S (fun v=>rawIntervalFamilyState π d σ (v,u))
    (fun v=>retainedRawFamilyState π d σ g₀ t J (v,u))
    (if a then some (Sum.inl g) else some (Sum.inr j))
  convert hh using 1
  · apply Finset.sum_congr rfl
    intro v hv
    cases a <;> simp only [bipAdj,rawMarkedSpokes,retainedRawMarkedSpokes,Bool.false_eq_true,ite_false,ite_true] <;> split_ifs <;> rfl
  · apply congrArg (fun n : ℕ=>(n:ℝ))
    apply congrArg Finset.card
    ext v
    simp only [Finset.mem_filter]

theorem retainedMarkedSpokes_restriction_changes {I : Type} [Fintype I]
    (π : Equiv.Perm V) (d : ℕ) (σ : RawIntervalFamilyOutcome V U Γ Color)
    (g₀ : Γ) (t : ℕ) (J : StartRetentionOutcome (rawStartHubSet π d σ g₀) t)
    (S : I→Finset V) (T : I→Finset U) (ζ : ℝ)
    (h : RetainedRestrictionGood π d σ g₀ t S T ζ J) (g : Γ) (j : Color) :
    ∀ i,(∀ a u,(∑ v∈S i,bipAdj (fun x u=>¬(rawMarkedSpokes π d σ g j a x u ↔
      retainedRawMarkedSpokes π d σ g₀ t J g j a x u)) v u)≤ζ*(S i).card) ∧
      (∀ a v,(∑ u∈T i,bipAdj (fun x u=>¬(rawMarkedSpokes π d σ g j a x u ↔
        retainedRawMarkedSpokes π d σ g₀ t J g j a x u)) v u)≤ζ*(T i).card) := by
  intro i
  exact ⟨fun a u=>(retainedMarkedSpokes_col_changes π d σ g₀ t J g j a u (S i)).trans ((h i).1 u),
    fun a v=>(retainedMarkedSpokes_row_changes π d σ g₀ t J g j a v (T i)).trans ((h i).2 v)⟩

end Oberwolfach
