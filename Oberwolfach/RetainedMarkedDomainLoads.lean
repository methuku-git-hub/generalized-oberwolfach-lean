module

public import Oberwolfach.RetainedMarkedRestrictionChanges
public import Oberwolfach.TypedMarkedPotentialDeletion

@[expose] public section

/-! Fixed potential loads on a smaller domain after global retention.
The coefficients and parent candidates are unchanged. The new local
spokes are restrictions of the global outcome, not new local samples. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color E K : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [Fintype E] [Fintype K]
  [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]
  {tail head : E→W} {ktail khead : K→W} {m b : ℕ} {H₀ Hₖ : W→Z→Prop}

variable (f : W↪oV) (g : Z↪U) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
  (hcomm : ∀ x,f (ρ x)=π (f x)) (d : ℕ) (σ : RawMarkedOutcome V U Γ Color)
  (g₀ : Γ) (t : ℕ)
  (J : StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g₀) t)
  (a : Γ) (j : Color) (δ : ℝ) (hδ : 0≤δ)
  (hrow : ∀ x,(((Finset.univ.image g).filter (fun u=>retainedRawFamilyState π d (fun e=>σ (Sum.inr e)) g₀ t J (x,u)≠
    rawIntervalFamilyState π d (fun e=>σ (Sum.inr e)) (x,u))).card:ℝ)≤δ)
  (hcol : ∀ u,(((Finset.univ.image f).filter (fun x=>retainedRawFamilyState π d (fun e=>σ (Sum.inr e)) g₀ t J (x,u)≠
    rawIntervalFamilyState π d (fun e=>σ (Sum.inr e)) (x,u))).card:ℝ)≤δ)
  (hm : 3≤m) (hn : 0<Fintype.card W)
  (w : MarkedWheel tail head ktail khead m ρ b H₀ Hₖ→ℝ) (B : ℝ) (hB : 0≤B)
  (hw : ∀ Q,0≤w Q ∧ w Q≤B/(Fintype.card W:ℝ)^m) (R : E⊕K→Prop)

include hcomm hδ hrow hcol hm hn hB hw

theorem retainedMarkedDomain_spoke_stability (c : Bool) (x : W) (u : Z) :
    |typedMarkedPotentialLoad w R
        (fun c x u=>retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g₀ t J a j c (f x) (g u))
        (Sum.inr (c,x,u))-
      typedMarkedPotentialLoad w R (rawMarkedPairSpokes ρ d (rawMarkedRestrictPair f g σ) a j)
        (Sum.inr (c,x,u))|≤5*((m:ℝ)+1)^4*B*δ/Fintype.card W := by
  apply typedMarkedPotentialLoad_spoke_degree_stability hm hn w B hB hw R R
    (rawMarkedPairSpokes ρ d (rawMarkedRestrictPair f g σ) a j)
    (fun c x u=>retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g₀ t J a j c (f x) (g u)) δ hδ
  · intro x;simpa using hδ
  · intro x;simpa using hδ
  · intro c x
    have hh := retainedMarked_restricted_row_changes f g π ρ hcomm d σ g₀ t J a j Finset.univ δ hrow c x
    convert hh using 1
    apply Finset.sum_congr rfl
    intro u hu
    unfold bipAdj
    split_ifs <;> rfl
  · intro c u
    have hh := retainedMarked_restricted_col_changes f g π ρ hcomm d σ g₀ t J a j Finset.univ δ hcol c u
    convert hh using 1
    apply Finset.sum_congr rfl
    intro x hx
    unfold bipAdj
    split_ifs <;> rfl

theorem retainedMarkedDomain_all_roots_stability (hu : Fintype.card Z≤Fintype.card W)
    (root : (E⊕K)⊕(Bool×W×Z)) :
    |typedMarkedPotentialLoad w R
        (fun c x u=>retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g₀ t J a j c (f x) (g u)) root-
      typedMarkedPotentialLoad w R (rawMarkedPairSpokes ρ d (rawMarkedRestrictPair f g σ) a j) root|≤
        11*((m:ℝ)+1)^4*B*δ/Fintype.card W := by
  apply typedMarkedPotentialLoad_degree_stability hm hn hu w B hB hw R R
    (rawMarkedPairSpokes ρ d (rawMarkedRestrictPair f g σ) a j)
    (fun c x u=>retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g₀ t J a j c (f x) (g u)) δ hδ
  · intro x;simpa using hδ
  · intro x;simpa using hδ
  · intro c x
    have hh := retainedMarked_restricted_row_changes f g π ρ hcomm d σ g₀ t J a j Finset.univ δ hrow c x
    convert hh using 1
    apply Finset.sum_congr rfl
    intro u hu
    unfold bipAdj
    split_ifs <;> rfl
  · intro c u
    have hh := retainedMarked_restricted_col_changes f g π ρ hcomm d σ g₀ t J a j Finset.univ δ hcol c u
    convert hh using 1
    apply Finset.sum_congr rfl
    intro x hx
    unfold bipAdj
    split_ifs <;> rfl

end Oberwolfach
