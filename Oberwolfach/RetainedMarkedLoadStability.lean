module

public import Oberwolfach.RetainedMarkedSpokeChanges
public import Oberwolfach.TypedMarkedPotentialDeletion

@[expose] public section

/-! Fixed root-omitted wheel loads after actual interval retention. The
physical rims and coefficients stay fixed. Newly exposed ordinary labels
are included in the symmetric-difference bounds. Spoke roots may lie at
any hub; their theorem requires no bound on the total number of hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color E K : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [Fintype E] [Fintype K] [DecidableEq V] [DecidableEq U]
  {tail head : E→V} {ktail khead : K→V} {m b : ℕ} {π : Equiv.Perm V}
  {H₀ Hₖ : V→U→Prop}

variable (d : ℕ) (σ : RawIntervalFamilyOutcome V U Γ Color) (g₀ : Γ) (t : ℕ)
  (J : StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (g : Γ) (j : Color)
  (δ : ℝ) (hδ : 0≤δ)
  (hrow : ∀ x,((Finset.univ.filter (fun u=>retainedRawFamilyState π d σ g₀ t J (x,u)≠
    rawIntervalFamilyState π d σ (x,u))).card:ℝ)≤δ)
  (hcol : ∀ u,((Finset.univ.filter (fun x=>retainedRawFamilyState π d σ g₀ t J (x,u)≠
    rawIntervalFamilyState π d σ (x,u))).card:ℝ)≤δ)
  (hm : 3≤m) (hn : 0<Fintype.card V)
  (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ→ℝ) (B : ℝ) (hB : 0≤B)
  (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m) (R : E⊕K→Prop)

include hδ hrow hcol hm hn hB hw

theorem retainedMarkedPotential_spoke_stability (a : Bool) (v : V) (u : U) :
    |typedMarkedPotentialLoad w R (retainedRawMarkedSpokes π d σ g₀ t J g j) (Sum.inr (a,v,u))-
      typedMarkedPotentialLoad w R (rawMarkedSpokes π d σ g j) (Sum.inr (a,v,u))|≤
        5*((m:ℝ)+1)^4*B*δ/Fintype.card V := by
  apply typedMarkedPotentialLoad_spoke_degree_stability hm hn w B hB hw R R
    (rawMarkedSpokes π d σ g j) (retainedRawMarkedSpokes π d σ g₀ t J g j) δ hδ
  · intro x;simpa using hδ
  · intro x;simpa using hδ
  · intro a x
    exact (retainedMarkedSpokes_row_changes π d σ g₀ t J g j a x Finset.univ).trans (hrow x)
  · intro a u
    exact (retainedMarkedSpokes_col_changes π d σ g₀ t J g j a u Finset.univ).trans (hcol u)

theorem retainedMarkedPotential_all_roots_stability (hu : Fintype.card U≤Fintype.card V)
    (root : (E⊕K)⊕(Bool×V×U)) :
    |typedMarkedPotentialLoad w R (retainedRawMarkedSpokes π d σ g₀ t J g j) root-
      typedMarkedPotentialLoad w R (rawMarkedSpokes π d σ g j) root|≤
        11*((m:ℝ)+1)^4*B*δ/Fintype.card V := by
  apply typedMarkedPotentialLoad_degree_stability hm hn hu w B hB hw R R
    (rawMarkedSpokes π d σ g j) (retainedRawMarkedSpokes π d σ g₀ t J g j) δ hδ
  · intro x;simpa using hδ
  · intro x;simpa using hδ
  · intro a x
    exact (retainedMarkedSpokes_row_changes π d σ g₀ t J g j a x Finset.univ).trans (hrow x)
  · intro a u
    exact (retainedMarkedSpokes_col_changes π d σ g₀ t J g j a u Finset.univ).trans (hcol u)

end Oberwolfach
