module

public import Oberwolfach.MarkedBalanceSpokeChanges

@[expose] public section
/-! Row and column concentration about their common probability centers
implies the full reference balance needed by the corrected host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_full_balance_from_centers
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (a b errR errS errC ε:ℝ)
    (hR0:0≤errR) (hS0:0≤errS) (hC0:0≤errC)
    (hR:∀mark incoming v,|(markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) mark incoming v Finset.univ:ℝ)-
      (if mark then a else (m:ℝ)*a)|≤errR)
    (hS:∀mark v,|(∑u,bipAdj (H mark) v u)-(if mark then a else (m:ℝ)*a)|≤errS)
    (hC:∀mark u,|(∑v,bipAdj (H mark) v u)-(if mark then b else (m:ℝ)*b)|≤errC)
    (hrowBudget:2*(errR+errS)≤ε) (hcolBudget:((m:ℝ)+1)*errC≤ε):
    MarkedRestrictedBalanceWithSpokes P π d m Finset.univ Finset.univ ε σ H:=by
  unfold MarkedRestrictedBalanceWithSpokes
  constructor
  · intro v
    constructor
    · intro incoming
      have hr0:=hR false incoming v
      have hr1:=hR true incoming v
      have hs0:=hS false v
      have hs1:=hS true v
      simp only [Bool.false_eq_true,↓reduceIte] at hr0 hr1 hs0 hs1
      have hr0a:=abs_le.mp hr0
      have hr1a:=abs_le.mp hr1
      have hs0a:=abs_le.mp hs0
      have hs1a:=abs_le.mp hs1
      apply abs_le.mpr
      constructor <;> linarith [hr0a.1,hr0a.2,hr1a.1,hr1a.2,hs0a.1,hs0a.2,hs1a.1,hs1a.2]
    · have hr:=hR true true v
      have hs:=hS true v
      simp only [↓reduceIte] at hr hs
      have hra:=abs_le.mp hr
      have hsa:=abs_le.mp hs
      apply abs_le.mpr
      constructor <;> linarith [hra.1,hra.2,hsa.1,hsa.2]
  · intro u
    have h0:=hC false u
    have h1:=hC true u
    simp only [Bool.false_eq_true,↓reduceIte] at h0 h1
    have h0a:=abs_le.mp h0
    have h1a:=abs_le.mp h1
    have hm:(0:ℝ)≤m:=Nat.cast_nonneg _
    have hlo:=mul_le_mul_of_nonneg_left h1a.1 hm
    have hhi:=mul_le_mul_of_nonneg_left h1a.2 hm
    apply abs_le.mpr
    constructor <;> nlinarith [h0a.1,h0a.2,hlo,hhi]
end Oberwolfach
