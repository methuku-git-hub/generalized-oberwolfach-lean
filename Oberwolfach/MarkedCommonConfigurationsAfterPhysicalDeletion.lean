module

public import Oberwolfach.MarkedCommonConfigurationSpokeChanges
public import Oberwolfach.MarkedSampleCommonPhysicalDeletion
public import Oberwolfach.MarkedPathRestrictionCounts

@[expose] public section

/-! Common configurations survive deletion of the actual physical rim and
spoke graphs. The original tuples, roots and directions are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_common_configurations_after_physical_deletion
    (r : ℕ) (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (β ζ δ : ℝ) (hδ : 0≤δ) (hn : 0<Fintype.card V)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (DR : SimpleGraph V) (DS : SimpleGraph (V⊕U))
    (hDR : ∀ x,(DR.degree x:ℝ)≤δ) (hDS : ∀ z,(DS.degree z:ℝ)≤δ)
    (hc : MarkedCommonConfigurationsWithSpokes r P π d β ζ σ H) :
    MarkedCommonConfigurationsWithSpokes r P π d β (ζ+4*δ/Fintype.card V)
      (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS) := by
  have hn0 : (Fintype.card V:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hnpos : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  constructor
  · intro C hC
    have hl := potentialMarkedHubs_change H (markedDeletePhysicalSpokes H DS) C δ (by
      intro b x
      have hh := (marked_spoke_physical_deletion_row_change H DS Finset.univ b x).trans (hDS (Sum.inl x))
      convert hh using 1
      apply Finset.sum_congr rfl
      intro u hu
      unfold bipAdj
      split_ifs <;> rfl)
    have hlo := (abs_le.mp hl).1
    have hh := hc.1 C hC
    have he : (32*β-(r+5:ℕ)*(ζ+4*δ/Fintype.card V))*Fintype.card V=
        (32*β-(r+5:ℕ)*ζ)*Fintype.card V-4*(r+5:ℕ)*δ := by
      field_simp
      <;> ring
    rw [he]
    push_cast at hlo hh ⊢
    nlinarith only [hlo,hh,hδ,mul_nonneg (show (0:ℝ)≤r by positivity) hδ]
  constructor
  · intro u hu
    have hh := hc.2.1 u hu
    have hl := marked_sample_common_cycle_physical_deletion P π d (r+4) (by omega)
      σ H DR DS δ hDR (fun u=>hDS (Sum.inr u)) (u 0) (u 1)
    change (Fintype.card (MarkedSampleCommonCycleWithSpokes P π d (r+4) σ H u):ℝ)-
      Fintype.card (MarkedSampleCommonCycleWithSpokes P π d (r+4)
        (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS) u)≤_ at hl
    have he : (16*β-2*(r+5:ℕ)*(ζ+4*δ/Fintype.card V))*(Fintype.card V:ℝ)^(r+5)=
        (16*β-2*(r+5:ℕ)*ζ)*(Fintype.card V:ℝ)^(r+5)-
          8*(r+5:ℕ)*δ*(Fintype.card V:ℝ)^(r+4) := by
      rw [show r+5=(r+4)+1 by omega,pow_succ]
      field_simp
      <;> ring
    rw [he]
    push_cast at hl hh ⊢
    nlinarith only [hl,hh,mul_nonneg (show (0:ℝ)≤r+5 by positivity)
      (mul_nonneg hδ (pow_nonneg hnpos.le (r+4)))]
  · intro v v' hv u hu j
    have hh := hc.2.2 v v' hv u hu j
    have hl := marked_sample_common_path_physical_deletion P π d (r+3+1) (by omega)
      σ H DR DS δ hDR (fun u=>hDS (Sum.inr u))
      ((markedRootOrder (r+3+1) j).symm 0) v v' (u 0) (u 1)
    have heOld : Fintype.card (MarkedSampleCommonPathWithSpokes P π d (r+3) σ H u j v v')=
      Fintype.card (CanonicalCommonMarkedPath
        (fun e : MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
        (fun e : MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
        (r+3+1) π (3*d) (H false) (H true) ((markedRootOrder (r+3+1) j).symm 0) v v' (u 0) (u 1)) :=
      Fintype.card_congr (rootFirstCommonMarkedPathCanonicalEquiv j v v' (u 0) (u 1))
    have heNew : Fintype.card (MarkedSampleCommonPathWithSpokes P π d (r+3)
        (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS) u j v v')=
      Fintype.card (CanonicalCommonMarkedPath
        (fun e : MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
        (fun e : MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
        (r+3+1) π (3*d) (markedDeletePhysicalSpokes H DS false) (markedDeletePhysicalSpokes H DS true)
        ((markedRootOrder (r+3+1) j).symm 0) v v' (u 0) (u 1)) :=
      Fintype.card_congr (rootFirstCommonMarkedPathCanonicalEquiv j v v' (u 0) (u 1))
    dsimp only at hl
    rw [←heOld,←heNew] at hl
    have he : (16*β-2*(r+4:ℕ)*(ζ+4*δ/Fintype.card V))*(Fintype.card V:ℝ)^(r+4)=
        (16*β-2*(r+4:ℕ)*ζ)*(Fintype.card V:ℝ)^(r+4)-
          8*(r+4:ℕ)*δ*(Fintype.card V:ℝ)^(r+3) := by
      rw [show r+4=(r+3)+1 by omega,pow_succ]
      field_simp
      <;> ring
    rw [he]
    simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hl hh ⊢
    nlinarith only [hl,hh,mul_nonneg hδ (pow_nonneg hnpos.le (r+3)),
      mul_nonneg (show (0:ℝ)≤r by positivity) (mul_nonneg hδ (pow_nonneg hnpos.le (r+3)))]

end Oberwolfach
