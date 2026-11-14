module

public import Oberwolfach.MarkedModifiedPhysicalIncidence

@[expose] public section
/-! Row counts on a fixed domain after arbitrary realised physical changes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_rows_after_physical_change
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (A:Finset V)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color)
    (errR deltaR deltaU:ℝ) (hR:0≤deltaR) (hU:0≤deltaU)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (hr:MarkedRowsWithSpokes P π d h A p k q s g j errR σ H)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hcr:∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈DR.edgeFinset)
    (hcs:∀ b v u,¬(H b v u↔H' b v u)→DS.Adj (Sum.inl v) (Sum.inr u))
    (hrim:∀ x,(DR.degree x:ℝ)≤deltaR)
    (hcol:∀ u,(DS.degree (Sum.inr u):ℝ)≤deltaU):
    MarkedRowsWithSpokes P π d h A p k q s g j (errR+h*(deltaR+deltaU)) τ H' := by
  have hr':=markedRows_rim_changes P π d h A p k q s g j errR deltaR hR σ τ H hr (by
    intro a
    calc
      _ ≤∑ x:V,if ¬(rawMarkedPairRims P π d σ (markedRowRim a x)↔rawMarkedPairRims P π d τ (markedRowRim a x)) then (1:ℝ) else 0:=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (by intro x _ _;positivity)
      _ ≤ (DR.degree (if a.1 && a.2.1 then π a.2.2 else a.2.2):ℝ):=
        marked_row_rim_physical_change P π d σ τ DR hcr a.1 a.2.1 a.2.2
      _ ≤ deltaR:=hrim _)
  obtain ⟨hsrow,hscol⟩:=marked_spoke_physical_change_incidence H H' DS hcs
  have hr'':=markedRows_spoke_relation_changes P π d h A p k q s g j
    (errR+h*deltaR) deltaU hU τ H H' hr' (by
      intro a u
      calc
        _ ≤∑ x:V,if ¬(H a x u↔H' a x u) then (1:ℝ) else 0:=by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
          intro x _ _; split_ifs <;> positivity
        _ ≤ (DS.degree (Sum.inr u):ℝ):=by
          convert hscol a u using 1
          apply Finset.sum_congr rfl
          intro x _
          unfold bipAdj
          split_ifs <;> simp_all
        _ ≤ deltaU:=hcol u)
  convert hr'' using 1 <;> ring
end Oberwolfach
