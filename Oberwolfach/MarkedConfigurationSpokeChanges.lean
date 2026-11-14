module

public import Oberwolfach.MarkedLocalClassChanges
public import Oberwolfach.RawMarkedLocalConfigurations

@[expose] public section

/-! Local configuration bounds after changes of the two spoke classes.
All free vertices are counted at the fixed inner-set scale; external path
roots and the omitted root spokes are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [LinearOrder V] [Fintype U]

theorem filter_sdiff_card_le_change_sum (A : Finset V) (P Q : V→Prop) :
    (((A.filter P)\(A.filter Q)).card:ℝ)≤
      ∑ x∈A,if ¬(P x ↔ Q x) then (1:ℝ) else 0 := by
  calc
    _ ≤ ((A.filter (fun x=>¬(P x↔Q x))).card:ℝ) := by
      exact_mod_cast Finset.card_le_card (show (A.filter P)\(A.filter Q)⊆A.filter (fun x=>¬(P x↔Q x)) from by
        intro x hx
        simp only [Finset.mem_sdiff,Finset.mem_filter] at hx ⊢
        exact ⟨hx.1.1,fun he=>hx.2 ⟨hx.1.1,he.mp hx.1.2⟩⟩)
    _ = _ := by simp only [Finset.sum_ite,Finset.sum_const,Finset.sum_const_zero,add_zero,nsmul_eq_mul,mul_one,mul_zero]

theorem markedLocalPhysicalCounts_class_changes
    (r b : ℕ) (P : SimpleGraph V) (π : Equiv.Perm V) (A : Finset V)
    (T₀ TK T₀' TK' : U→Finset V)
    (hT₀ : ∀ u,T₀ u⊆A) (hTK : ∀ u,TK u⊆A)
    (hT₀' : ∀ u,T₀' u⊆A) (hTK' : ∀ u,TK' u⊆A)
    (βC βP ζ : ℝ) (hD₀ : ∀ u,((T₀ u\T₀' u).card:ℝ)≤ζ*A.card)
    (hDK : ∀ u,((TK u\TK' u).card:ℝ)≤ζ*A.card)
    (σ : Sym2 V→Option (Bool×Bool))
    (hc : MarkedLocalPhysicalCounts r b P π T₀ TK A.card βC βP σ) :
    MarkedLocalPhysicalCounts r b P π T₀' TK' A.card
      (βC-(r+5:ℕ)*ζ) (βP-(r+4:ℕ)*ζ) σ := by
  constructor
  · intro u
    have hl := markedLocalBase_class_loss P π b (r+4) A (T₀ u) (TK u) (T₀' u) (TK' u)
      (hT₀ u) (hTK u) (hT₀' u) (hTK' u) (ζ*A.card) (hD₀ u) (hDK u) σ
    have he : (((r+4:ℕ):ℝ)+1)*(ζ*A.card)*(A.card:ℝ)^(r+4)=
        (r+5:ℕ)*ζ*(A.card:ℝ)^(r+5) := by
      simp only [Nat.cast_add,Nat.cast_ofNat,show r+5=(r+4)+1 by omega,pow_succ]
      ring
    rw [he] at hl
    have hh := hc.1 u
    nlinarith only [hh,hl]
  · intro u j v v' hv
    have hl := markedLocalPath_class_loss P π b (r+3) j v v' A (T₀ u) (TK u) (T₀' u) (TK' u)
      (hT₀ u) (hTK u) (hT₀' u) (hTK' u) (ζ*A.card) (hD₀ u) (hDK u) σ
    have he : (((r+3:ℕ):ℝ)+1)*(ζ*A.card)*(A.card:ℝ)^(r+3)=
        (r+4:ℕ)*ζ*(A.card:ℝ)^(r+4) := by
      simp only [Nat.cast_add,Nat.cast_ofNat,show r+4=(r+3)+1 by omega,pow_succ]
      ring
    rw [he] at hl
    have hh := hc.2 u j v v' hv
    nlinarith only [hh,hl]

variable {Γ Color : Type} [Fintype Γ] [Fintype Color] [DecidableEq U]

def MarkedLocalConfigurationsWithSpokes (r : ℕ) (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (A : Finset V) (βC βP : ℝ) (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop) : Prop :=
  MarkedLocalPhysicalCounts r (3*d) P π (fun u=>A.filter (H false · u))
    (fun u=>A.filter (H true · u)) A.card βC βP (fun e=>σ (Sum.inl e))

theorem markedLocalConfigurations_spoke_changes
    (r : ℕ) (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (a : Γ) (j : Color) (A : Finset V) (βC βP ζ : ℝ)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (hc : RawMarkedLocalConfigurations r P π d a j A βC βP σ)
    (hchange : ∀ b u,(∑ x∈A,if ¬(rawMarkedPairSpokes π d σ a j b x u ↔ H b x u)
      then (1:ℝ) else 0)≤ζ*A.card) :
    MarkedLocalConfigurationsWithSpokes r P π d A (βC-(r+5:ℕ)*ζ) (βP-(r+4:ℕ)*ζ) σ H := by
  apply markedLocalPhysicalCounts_class_changes r (3*d) P π A
    (fun u=>A.filter (fun x=>rawMarkedPairSpokes π d σ a j false x u))
    (fun u=>A.filter (fun x=>rawMarkedPairSpokes π d σ a j true x u))
    (fun u=>A.filter (H false · u)) (fun u=>A.filter (H true · u))
    (fun _=>Finset.filter_subset _ _) (fun _=>Finset.filter_subset _ _)
    (fun _=>Finset.filter_subset _ _) (fun _=>Finset.filter_subset _ _) βC βP ζ
  · intro u
    exact (filter_sdiff_card_le_change_sum A _ _).trans (hchange false u)
  · intro u
    exact (filter_sdiff_card_le_change_sum A _ _).trans (hchange true u)
  · exact hc

end Oberwolfach
