module

public import Oberwolfach.RawMarkedRestrictedBalance
public import Oberwolfach.MarkedNeighbourhoodSpokeChanges

@[expose] public section

/-! Restricted balance after arbitrary spoke changes. The physical rim
degrees remain fixed; both gains and losses of either spoke type count
against the original row and hub domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem indicator_sum_change {X : Type*} (A : Finset X) (P Q : X→Prop) :
    |(∑ x∈A,if Q x then (1:ℝ) else 0)-(∑ x∈A,if P x then (1:ℝ) else 0)|≤
      ∑ x∈A,if ¬(P x↔Q x) then (1:ℝ) else 0 := by
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro x hx
  by_cases hp : P x <;> by_cases hq : Q x <;> simp [hp,hq]

theorem sum_balance_spoke_change (r x y x' y' ε δ : ℝ)
    (h : |r-(x+y)|≤ε) (hx : |x'-x|≤δ) (hy : |y'-y|≤δ) :
    |r-(x'+y')|≤ε+2*δ := by
  rcases abs_le.mp h with ⟨h1,h2⟩
  rcases abs_le.mp hx with ⟨hx1,hx2⟩
  rcases abs_le.mp hy with ⟨hy1,hy2⟩
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem ratio_balance_spoke_change (x y x' y' m ε δ : ℝ) (hm : 0≤m)
    (h : |x-m*y|≤ε) (hx : |x'-x|≤δ) (hy : |y'-y|≤δ) :
    |x'-m*y'|≤ε+(m+1)*δ := by
  rcases abs_le.mp h with ⟨h1,h2⟩
  rcases abs_le.mp hx with ⟨hx1,hx2⟩
  rcases abs_le.mp hy with ⟨hy1,hy2⟩
  have hm1 := mul_le_mul_of_nonneg_left hy1 hm
  have hm2 := mul_le_mul_of_nonneg_left hy2 hm
  exact abs_le.mpr ⟨by nlinarith only [h1,hx1,hm2],by nlinarith only [h2,hx2,hm1]⟩

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem rawMarkedRestrictedSpokeRow_eq_sum (π : Equiv.Perm V) (d : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (g : Γ) (j : Color) (b : Bool) (x : V) (B : Finset U) :
    rawMarkedRestrictedSpokeRow π d (fun e=>σ (Sum.inr e)) g j b x B=
      ∑ u∈B,bipAdj (rawMarkedPairSpokes π d σ g j b) x u := by
  unfold rawMarkedRestrictedSpokeRow
  apply Finset.sum_congr rfl
  intro u hu
  cases b <;> simp only [bipAdj,rawMarkedPairSpokes,rawMarkedSpokes,Bool.false_eq_true,ite_false,ite_true] <;> split_ifs <;> rfl

theorem rawMarkedRestrictedSpokeCol_eq_sum (π : Equiv.Perm V) (d : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (g : Γ) (j : Color) (b : Bool) (u : U) (A : Finset V) :
    rawMarkedRestrictedSpokeCol π d (fun e=>σ (Sum.inr e)) g j b u A=
      ∑ x∈A,bipAdj (rawMarkedPairSpokes π d σ g j b) x u := by
  unfold rawMarkedRestrictedSpokeCol
  apply Finset.sum_congr rfl
  intro x hx
  cases b <;> simp only [bipAdj,rawMarkedPairSpokes,rawMarkedSpokes,Bool.false_eq_true,ite_false,ite_true] <;> split_ifs <;> rfl

def MarkedRestrictedBalanceWithSpokes (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ)
    (A : Finset V) (B : Finset U) (η : ℝ) (σ : RawMarkedOutcome V U Γ Color)
    (H : Bool→V→U→Prop) : Prop :=
  let R := fun mark incoming x=>(markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) mark incoming x A:ℝ)
  let HR := fun b x=>∑ u∈B,bipAdj (H b) x u
  let HC := fun b u=>∑ x∈A,bipAdj (H b) x u
  (∀ x,(∀ incoming,|R false incoming x+R true incoming x-(HR false x+HR true x)|≤η) ∧
    |R true true x-HR true x|≤η) ∧ (∀ u,|HC false u-(m:ℝ)*HC true u|≤η)

theorem markedRestrictedBalance_spoke_changes (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ)
    (A : Finset V) (B : Finset U) (g : Γ) (j : Color) (η δ : ℝ) (hδ : 0≤δ)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (hraw : RawMarkedRestrictedBalance P π d m g j A B η σ)
    (hrow : ∀ b x,(∑ u∈B,if ¬(rawMarkedPairSpokes π d σ g j b x u↔H b x u) then (1:ℝ) else 0)≤δ)
    (hcol : ∀ b u,(∑ x∈A,if ¬(rawMarkedPairSpokes π d σ g j b x u↔H b x u) then (1:ℝ) else 0)≤δ) :
    MarkedRestrictedBalanceWithSpokes P π d m A B (η+(m+2:ℕ)*δ) σ H := by
  have hr (b : Bool) (x : V) :
      |(∑ u∈B,bipAdj (H b) x u)-rawMarkedRestrictedSpokeRow π d (fun e=>σ (Sum.inr e)) g j b x B|≤δ := by
    rw [rawMarkedRestrictedSpokeRow_eq_sum]
    have hh := (indicator_sum_change B (fun u=>rawMarkedPairSpokes π d σ g j b x u) (fun u=>H b x u)).trans (hrow b x)
    convert hh using 1
    apply congrArg abs
    apply congrArg₂ (fun a b : ℝ=>a-b) <;> apply Finset.sum_congr rfl <;> intro u hu <;> unfold bipAdj <;> split_ifs <;> rfl
  have hc (b : Bool) (u : U) :
      |(∑ x∈A,bipAdj (H b) x u)-rawMarkedRestrictedSpokeCol π d (fun e=>σ (Sum.inr e)) g j b u A|≤δ := by
    rw [rawMarkedRestrictedSpokeCol_eq_sum]
    have hh := (indicator_sum_change A (fun x=>rawMarkedPairSpokes π d σ g j b x u) (fun x=>H b x u)).trans (hcol b u)
    convert hh using 1
    apply congrArg abs
    apply congrArg₂ (fun a b : ℝ=>a-b) <;> apply Finset.sum_congr rfl <;> intro x hx <;> unfold bipAdj <;> split_ifs <;> rfl
  constructor
  · intro x
    constructor
    · intro incoming
      have hh := sum_balance_spoke_change _ _ _ _ _ η δ ((hraw.1 x).1 incoming) (hr false x) (hr true x)
      exact hh.trans (by push_cast; nlinarith only [mul_nonneg (Nat.cast_nonneg m : (0:ℝ)≤m) hδ])
    · have hh := abs_sub_le
        (markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) true true x A:ℝ)
        (rawMarkedRestrictedSpokeRow π d (fun e=>σ (Sum.inr e)) g j true x B)
        (∑ u∈B,bipAdj (H true) x u)
      rw [abs_sub_comm (rawMarkedRestrictedSpokeRow _ _ _ _ _ _ _ _)] at hh
      exact hh.trans ((add_le_add ((hraw.1 x).2) (hr true x)).trans
        (by push_cast; nlinarith only [mul_nonneg (Nat.cast_nonneg m : (0:ℝ)≤m) hδ,hδ]))
  · intro u
    have hh := ratio_balance_spoke_change _ _ _ _ (m:ℝ) η δ (by positivity) (hraw.2 u) (hc false u) (hc true u)
    exact hh.trans (by push_cast;linarith only [hδ])

end Oberwolfach
