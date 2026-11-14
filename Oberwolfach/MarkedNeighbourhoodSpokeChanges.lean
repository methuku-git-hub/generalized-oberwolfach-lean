module

public import Oberwolfach.FiniteConjunctionChanges
public import Oberwolfach.MarkedRowCommonEvent
public import Oberwolfach.MarkedIndexCommonEvent

@[expose] public section

/-! Neighbourhood estimates under an arbitrary change of spoke relations.
This applies to restrictions of one globally retained sample; the new
relations need not come from uniform retention on the smaller domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def markedRowCountWithSpokes (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (C : Finset V) (S : Finset (Bool×Bool×V)) (J : Finset (Bool×U)) : ℝ :=
  ∑ x∈C,if (∀ a∈S,rawMarkedPairRims P π d σ (markedRowRim a x)) ∧
    (∀ a∈J,H a.1 x a.2) then 1 else 0

def markedIndexCountWithSpokes (H : Bool→V→U→Prop) (B : Finset U) (J : Finset (Bool×V)) : ℝ :=
  ∑ u∈B,if ∀ a∈J,H a.1 a.2 u then 1 else 0

def MarkedRowsWithSpokes (P : SimpleGraph V) (π : Equiv.Perm V) (d h : ℕ)
    (A : Finset V) (p k : ℝ) (q : U→Γ→ℝ) (s : U→Color→ℝ) (g : Γ) (j : Color) (ε : ℝ)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop) : Prop :=
  ∀ (S T : Finset (Bool×Bool×V)) (J : Finset (Bool×U)),
    S.card≤h → T.card≤h → J.card≤h → Set.InjOn (fun a : Bool×U=>a.2) J →
    |markedRowCountWithSpokes P π d σ H (markedRowDomain P π (3*d) A S T) S J-
      (∏ a∈S,if a.1 then k else p)*(∏ a∈J,if a.1 then q a.2 g else s a.2 j)*
        (markedRowDomain P π (3*d) A S T).card|<ε

def MarkedIndicesWithSpokes (π : Equiv.Perm V) (d h : ℕ) (B : Finset U)
    (q : U→Γ→ℝ) (s : U→Color→ℝ) (g : Γ) (j : Color) (ε : ℝ)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop) : Prop :=
  ∀ J : Finset (Bool×V),J.card≤h →
    (∀ a∈J,∀ b∈J,a≠b → ¬PermutationClose π (3*d) a.2 b.2) →
    |markedIndexCountWithSpokes H B J-∑ u∈B,∏ a∈J,if a.1 then q u g else s u j|<ε

theorem markedRowCountWithSpokes_change (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (A C : Finset V) (hCA : C⊆A) (S : Finset (Bool×Bool×V)) (J : Finset (Bool×U))
    (g : Γ) (j : Color) (δ : ℝ)
    (hδ : ∀ a∈J,(∑ x∈A,if ¬(rawMarkedPairSpokes π d σ g j a.1 x a.2 ↔ H a.1 x a.2) then (1:ℝ) else 0)≤δ) :
    |markedRowCountWithSpokes P π d σ H C S J-rawMarkedRowCount P π d C S J g j σ|≤J.card*δ := by
  have hh := finiteConjunction_sum_change_at_outer A C hCA J
    (fun x=>∀ a∈S,rawMarkedPairRims P π d σ (markedRowRim a x))
    (fun a x=>rawMarkedPairSpokes π d σ g j a.1 x a.2) (fun a x=>H a.1 x a.2) δ hδ
  convert hh using 1
  apply congrArg abs
  apply congrArg₂ (fun x y : ℝ=>x-y)
  · unfold markedRowCountWithSpokes
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs <;> rfl
  · unfold rawMarkedRowCount
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs <;> rfl

theorem markedIndexCountWithSpokes_change (π : Equiv.Perm V) (d : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (B : Finset U) (J : Finset (Bool×V)) (g : Γ) (j : Color) (δ : ℝ)
    (hδ : ∀ a∈J,(∑ u∈B,if ¬(rawMarkedPairSpokes π d σ g j a.1 a.2 u ↔ H a.1 a.2 u) then (1:ℝ) else 0)≤δ) :
    |markedIndexCountWithSpokes H B J-rawMarkedIndexCount π d B J g j σ|≤J.card*δ := by
  have hh := finiteConjunction_sum_change_at_outer B B (fun _ h=>h) J (fun _=>True)
    (fun a u=>rawMarkedPairSpokes π d σ g j a.1 a.2 u) (fun a u=>H a.1 a.2 u) δ hδ
  simpa only [true_and,markedIndexCountWithSpokes,rawMarkedIndexCount] using hh

theorem markedRows_spoke_changes (P : SimpleGraph V) (π : Equiv.Perm V) (d h : ℕ)
    (A : Finset V) (p k : ℝ) (q : U→Γ→ℝ) (s : U→Color→ℝ) (g : Γ) (j : Color) (ε δ : ℝ)
    (hδ0 : 0≤δ) (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (hraw : RawMarkedRows P π d h A p k q s g j ε σ)
    (hchange : ∀ a u,(∑ x∈A,if ¬(rawMarkedPairSpokes π d σ g j a x u ↔ H a x u) then (1:ℝ) else 0)≤δ) :
    MarkedRowsWithSpokes P π d h A p k q s g j (ε+h*δ) σ H := by
  intro S T J hS hT hJ hinj
  let C := markedRowDomain P π (3*d) A S T
  have hc := markedRowCountWithSpokes_change P π d σ H A C (Finset.filter_subset _ _) S J g j δ
    (fun a _=>hchange a.1 a.2)
  have hcard : (J.card:ℝ)≤h := by exact_mod_cast hJ
  have hb := mul_le_mul_of_nonneg_right hcard hδ0
  have he := hraw S T J hS hT hJ hinj
  have hh := (abs_sub_le (markedRowCountWithSpokes P π d σ H C S J)
    (rawMarkedRowCount P π d C S J g j σ)
    ((∏ a∈S,if a.1 then k else p)*(∏ a∈J,if a.1 then q a.2 g else s a.2 j)*C.card)).trans_lt
      (add_lt_add_of_le_of_lt (hc.trans hb) he)
  convert hh using 1 <;> ring

theorem markedIndices_spoke_changes (π : Equiv.Perm V) (d h : ℕ) (B : Finset U)
    (q : U→Γ→ℝ) (s : U→Color→ℝ) (g : Γ) (j : Color) (ε δ : ℝ)
    (hδ0 : 0≤δ) (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (hraw : RawMarkedIndices π d h B q s g j ε σ)
    (hchange : ∀ a x,(∑ u∈B,if ¬(rawMarkedPairSpokes π d σ g j a x u ↔ H a x u) then (1:ℝ) else 0)≤δ) :
    MarkedIndicesWithSpokes π d h B q s g j (ε+h*δ) σ H := by
  intro J hJ hsep
  have hc := markedIndexCountWithSpokes_change π d σ H B J g j δ (fun a _=>hchange a.1 a.2)
  have hcard : (J.card:ℝ)≤h := by exact_mod_cast hJ
  have hb := mul_le_mul_of_nonneg_right hcard hδ0
  have he := hraw J hJ hsep
  have hh := (abs_sub_le (markedIndexCountWithSpokes H B J)
    (rawMarkedIndexCount π d B J g j σ) (∑ u∈B,∏ a∈J,if a.1 then q u g else s u j)).trans_lt
      (add_lt_add_of_le_of_lt (hc.trans hb) he)
  convert hh using 1 <;> ring

end Oberwolfach
