module

public import Oberwolfach.RetainedMarkedNeighbourhoods

@[expose] public section

/-! Every bounded row or index test survives retention with the original
product target. The deterministic transfer is simultaneous over all tests;
no event is selected after their roots are chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def RetainedMarkedRows (P : SimpleGraph V) (π : Equiv.Perm V) (d h : ℕ)
    (A : Finset V) (p k : ℝ) (q : U→Γ→ℝ) (s : U→Color→ℝ) (g : Γ) (j : Color) (ε : ℝ)
    (σ : RawMarkedOutcome V U Γ Color) (g₀ : Γ) (t : ℕ)
    (K : StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g₀) t) : Prop :=
  ∀ (S T : Finset (Bool×Bool×V)) (J : Finset (Bool×U)),
    S.card≤h → T.card≤h → J.card≤h → Set.InjOn (fun a : Bool×U=>a.2) J →
    |retainedMarkedRowCount P π d σ g₀ t K (markedRowDomain P π (3*d) A S T) S J g j-
      (∏ a∈S,if a.1 then k else p)*(∏ a∈J,if a.1 then q a.2 g else s a.2 j)*
        (markedRowDomain P π (3*d) A S T).card|<ε

def RetainedMarkedIndices (π : Equiv.Perm V) (d h : ℕ) (B : Finset U)
    (q : U→Γ→ℝ) (s : U→Color→ℝ) (g : Γ) (j : Color) (ε : ℝ)
    (σ : RawMarkedOutcome V U Γ Color) (g₀ : Γ) (t : ℕ)
    (K : StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g₀) t) : Prop :=
  ∀ J : Finset (Bool×V),J.card≤h →
    (∀ a∈J,∀ b∈J,a≠b → ¬PermutationClose π (3*d) a.2 b.2) →
    |retainedMarkedIndexCount π d σ g₀ t K B J g j-
      ∑ u∈B,∏ a∈J,if a.1 then q u g else s u j|<ε

theorem retainedMarkedRows_of_raw (P : SimpleGraph V) (π : Equiv.Perm V) (d h : ℕ)
    (A : Finset V) (p k : ℝ) (q : U→Γ→ℝ) (s : U→Color→ℝ) (g : Γ) (j : Color) (ε ζ : ℝ)
    (hζ : 0≤ζ) (σ : RawMarkedOutcome V U Γ Color) (g₀ : Γ) (t : ℕ)
    (K : StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g₀) t)
    (hraw : RawMarkedRows P π d h A p k q s g j ε σ)
    (hchange : ∀ u,((A.filter (fun x=>retainedRawFamilyState π d (fun e=>σ (Sum.inr e)) g₀ t K (x,u)≠
      rawIntervalFamilyState π d (fun e=>σ (Sum.inr e)) (x,u))).card:ℝ)≤ζ*A.card) :
    RetainedMarkedRows P π d h A p k q s g j (ε+h*ζ*A.card) σ g₀ t K := by
  intro S T J hS hT hJ hinj
  let C := markedRowDomain P π (3*d) A S T
  have hCA : C⊆A := Finset.filter_subset _ _
  have hc := retainedMarkedRowCount_change P π d σ g₀ t K A C hCA S J g j (ζ*A.card) hchange
  have hcard : (J.card:ℝ)≤h := by exact_mod_cast hJ
  have hb := mul_le_mul_of_nonneg_right hcard (show 0≤ζ*A.card by positivity)
  have he := hraw S T J hS hT hJ hinj
  have hh := (abs_sub_le (retainedMarkedRowCount P π d σ g₀ t K C S J g j)
    (rawMarkedRowCount P π d C S J g j σ)
    ((∏ a∈S,if a.1 then k else p)*(∏ a∈J,if a.1 then q a.2 g else s a.2 j)*C.card)).trans_lt
      (add_lt_add_of_le_of_lt (hc.trans hb) he)
  convert hh using 1 <;> ring

theorem retainedMarkedIndices_of_raw (π : Equiv.Perm V) (d h : ℕ) (B : Finset U)
    (q : U→Γ→ℝ) (s : U→Color→ℝ) (g : Γ) (j : Color) (ε ζ : ℝ)
    (hζ : 0≤ζ) (σ : RawMarkedOutcome V U Γ Color) (g₀ : Γ) (t : ℕ)
    (K : StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g₀) t)
    (hraw : RawMarkedIndices π d h B q s g j ε σ)
    (hchange : ∀ x,((B.filter (fun u=>retainedRawFamilyState π d (fun e=>σ (Sum.inr e)) g₀ t K (x,u)≠
      rawIntervalFamilyState π d (fun e=>σ (Sum.inr e)) (x,u))).card:ℝ)≤ζ*B.card) :
    RetainedMarkedIndices π d h B q s g j (ε+h*ζ*B.card) σ g₀ t K := by
  intro J hJ hsep
  have hc := retainedMarkedIndexCount_change π d σ g₀ t K B J g j (ζ*B.card) hchange
  have hcard : (J.card:ℝ)≤h := by exact_mod_cast hJ
  have hb := mul_le_mul_of_nonneg_right hcard (show 0≤ζ*B.card by positivity)
  have he := hraw J hJ hsep
  have hh := (abs_sub_le (retainedMarkedIndexCount π d σ g₀ t K B J g j)
    (rawMarkedIndexCount π d B J g j σ) (∑ u∈B,∏ a∈J,if a.1 then q u g else s u j)).trans_lt
      (add_lt_add_of_le_of_lt (hc.trans hb) he)
  convert hh using 1 <;> ring

end Oberwolfach
