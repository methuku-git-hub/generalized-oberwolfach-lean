module

public import Oberwolfach.TwoHubTupleChanges
public import Oberwolfach.MarkedReferenceConfigurations
public import Oberwolfach.MarkedPotentialHubStability

@[expose] public section

/-! The actual compatible-hub, two-hub cycle and root-omitted common-path
families after spoke changes. Physical arc identifiers and directions are
unchanged, and the two roots need not have any spokes present. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

abbrev MarkedSampleCommonCycleWithSpokes (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop) (u : Fin 2→U) :=
  CommonMarkedCycle
    (fun e : MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
    (fun e : MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
    m π (3*d) (H false) (H true) (u 0) (u 1)

abbrev MarkedSampleCommonPathWithSpokes (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop) (u : Fin 2→U)
    (j : Bool) (v v' : V) :=
  RootFirstCommonMarkedPath
    (fun e : MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
    (fun e : MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
    (m+1) π (3*d) (H false) (H true) j v v' (u 0) (u 1)

def MarkedCommonConfigurationsWithSpokes (r : ℕ) (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (β ζ : ℝ) (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop) : Prop :=
  (∀ C : Fin (r+5)→V,PermutationSeparated π (3*d) C →
    (32*β-(r+5:ℕ)*ζ)*Fintype.card V≤((potentialMarkedHubs H C).card:ℝ)) ∧
  (∀ u : Fin 2→U,Function.Injective u →
    (16*β-2*(r+5:ℕ)*ζ)*(Fintype.card V:ℝ)^(r+5)≤
      (Fintype.card (MarkedSampleCommonCycleWithSpokes P π d (r+4) σ H u):ℝ)) ∧
  (∀ v v' : V,v≠v' → ∀ u : Fin 2→U,Function.Injective u → ∀ j : Bool,
    (16*β-2*(r+4:ℕ)*ζ)*(Fintype.card V:ℝ)^(r+4)≤
      (Fintype.card (MarkedSampleCommonPathWithSpokes P π d (r+3) σ H u j v v'):ℝ))

theorem markedCommonConfigurations_spoke_changes
    (r : ℕ) (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (a : Γ) (j : Color)
    (β ζ : ℝ) (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (hraw : MarkedReferenceConfigurations r P π d a j β σ)
    (hrow : ∀ b x,(∑ u,if ¬(rawMarkedPairSpokes π d σ a j b x u↔H b x u) then (1:ℝ) else 0)≤ζ*Fintype.card V)
    (hcol : ∀ b u,(∑ x,if ¬(rawMarkedPairSpokes π d σ a j b x u↔H b x u) then (1:ℝ) else 0)≤ζ*Fintype.card V) :
    MarkedCommonConfigurationsWithSpokes r P π d β ζ σ H := by
  constructor
  · intro C hC
    have hh := potentialMarkedHubs_change (rawMarkedPairSpokes π d σ a j) H C (ζ*Fintype.card V) (by
      intro b x
      convert hrow b x using 1
      apply Finset.sum_congr rfl
      intro u hu
      unfold bipAdj
      split_ifs <;> rfl)
    have hlo := (abs_le.mp hh).1
    have hc := hraw.1 C hC
    push_cast at hlo hc ⊢
    nlinarith only [hlo,hc]
  constructor
  · intro u hu
    have he : Fintype.card (SampledCommonMarkedCycle P π d (r+4)
        (fun e=>σ (Sum.inr e)) (fun e=>σ (Sum.inl e)) a j u)=
        Fintype.card (MarkedSampleCommonCycleWithSpokes P π d (r+4) σ (rawMarkedPairSpokes π d σ a j) u) := by
      apply Fintype.card_congr
      apply Equiv.subtypeEquivRight
      intro C
      rw [Fin.forall_fin_two]
      rfl
    have hc := hraw.2.1 u hu
    rw [he] at hc
    have hl := commonMarkedCycle_spoke_changes
      (fun e : MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e : MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
      (r+4) π (3*d) (rawMarkedPairSpokes π d σ a j) H (u 0) (u 1) (ζ*Fintype.card V) hcol
    have heq : 2*(((r+4:ℕ):ℝ)+1)*(ζ*Fintype.card V)*(Fintype.card V:ℝ)^(r+4)=
        2*(r+5:ℕ)*ζ*(Fintype.card V:ℝ)^(r+5) := by
      simp only [Nat.cast_add,Nat.cast_ofNat,show r+5=(r+4)+1 by omega,pow_succ]
      ring
    rw [heq] at hl
    change (Fintype.card (MarkedSampleCommonCycleWithSpokes P π d (r+4) σ (rawMarkedPairSpokes π d σ a j) u):ℝ)-
      Fintype.card (MarkedSampleCommonCycleWithSpokes P π d (r+4) σ H u)≤_ at hl
    nlinarith only [hc,hl]
  · intro v v' hv u hu b
    have hc := hraw.2.2 v v' hv u hu b
    change (16*β)*(Fintype.card V:ℝ)^(r+4)≤
      (Fintype.card (MarkedSampleCommonPathWithSpokes P π d (r+3) σ (rawMarkedPairSpokes π d σ a j) u b v v'):ℝ) at hc
    have hl := rootFirstCommonMarkedPath_spoke_changes
      (fun e : MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e : MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
      ((r+3)+1) π (3*d) (rawMarkedPairSpokes π d σ a j) H b v v' (u 0) (u 1) (ζ*Fintype.card V) hcol
    have heq : 2*((r+3+1:ℕ):ℝ)*(ζ*Fintype.card V)*(Fintype.card V:ℝ)^(r+3+1-1)=
        2*(r+4:ℕ)*ζ*(Fintype.card V:ℝ)^(r+4) := by
      simp only [Nat.add_sub_cancel,show r+4=(r+3)+1 by omega,pow_succ]
      ring
    rw [heq] at hl
    change (Fintype.card (MarkedSampleCommonPathWithSpokes P π d (r+3) σ (rawMarkedPairSpokes π d σ a j) u b v v'):ℝ)-
      Fintype.card (MarkedSampleCommonPathWithSpokes P π d (r+3) σ H u b v v')≤_ at hl
    nlinarith only [hc,hl]

end Oberwolfach
