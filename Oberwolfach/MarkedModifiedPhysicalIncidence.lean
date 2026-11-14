module

public import Oberwolfach.MarkedPotentialPhysicalDeletion
public import Oberwolfach.MarkedModifiedLocalLoadBridge

@[expose] public section
/-! A physical change graph controls the typed incidences even if edges are
added, removed, reversed or retyped. No sampling is involved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_row_rim_physical_change
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color) (D:SimpleGraph V)
    (hchange:∀ a, ¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a) →
      markedPairPhysical π a∈D.edgeFinset)
    (mark incoming:Bool) (v:V):
    (∑ x:V,if ¬(rawMarkedPairRims P π d σ (markedRowRim (mark,incoming,v) x)↔
      rawMarkedPairRims P π d τ (markedRowRim (mark,incoming,v) x)) then (1:ℝ) else 0)
      ≤D.degree (if mark && incoming then π v else v):=by
  calc
    _ ≤∑ x:V,if markedPairPhysical π (markedRowRim (mark,incoming,v) x)∈D.edgeFinset then (1:ℝ) else 0:=by
      apply Finset.sum_le_sum
      intro x _
      by_cases h:¬(rawMarkedPairRims P π d σ (markedRowRim (mark,incoming,v) x)↔
        rawMarkedPairRims P π d τ (markedRowRim (mark,incoming,v) x))
      · simp [h,hchange _ h]
      · simp [h]; positivity
    _ = _:=marked_row_physical_coordinate_degree π D mark incoming v

theorem marked_spoke_physical_change_incidence
    (H H':Bool→V→U→Prop) (D:SimpleGraph (V⊕U))
    (hchange:∀ b v u,¬(H b v u↔H' b v u)→D.Adj (Sum.inl v) (Sum.inr u)):
    (∀ b v,(∑ u,bipAdj (fun x u=>¬(H b x u↔H' b x u)) v u)≤(D.degree (Sum.inl v):ℝ)) ∧
    (∀ b u,(∑ v,bipAdj (fun x u=>¬(H b x u↔H' b x u)) v u)≤(D.degree (Sum.inr u):ℝ)):=by
  constructor
  · intro b v
    calc
      _ ≤∑ u:U,if D.Adj (Sum.inl v) (Sum.inr u) then (1:ℝ) else 0:=by
        apply Finset.sum_le_sum
        intro u _
        by_cases h:¬(H b v u↔H' b v u)
        · simp [bipAdj,h,hchange _ _ _ h]
        · simp [bipAdj,h]; positivity
      _ = ((Finset.univ.filter (fun u=>D.Adj (Sum.inl v) (Sum.inr u))).card:ℝ):=by
        simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
      _ ≤_:=Nat.cast_le.mpr (physical_spoke_deleted_row D v)
  · intro b u
    calc
      _ ≤∑ v:V,if D.Adj (Sum.inl v) (Sum.inr u) then (1:ℝ) else 0:=by
        apply Finset.sum_le_sum
        intro v _
        by_cases h:¬(H b v u↔H' b v u)
        · simp [bipAdj,h,hchange _ _ _ h]
        · simp [bipAdj,h]; positivity
      _ = ((Finset.univ.filter (fun v=>D.Adj (Sum.inl v) (Sum.inr u))).card:ℝ):=by
        simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
      _ ≤_:=Nat.cast_le.mpr (physical_spoke_deleted_col D u)
theorem marked_neighbourhoods_after_physical_change
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (A:Finset V) (B:Finset U)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color)
    (errR errI deltaR deltaV deltaU:ℝ) (hR:0≤deltaR) (hV:0≤deltaV) (hU:0≤deltaU)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (hr:MarkedRowsWithSpokes P π d h A p k q s g j errR σ H)
    (hi:MarkedIndicesWithSpokes π d h B q s g j errI σ H)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hcr:∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a) →
      markedPairPhysical π a∈DR.edgeFinset)
    (hcs:∀ b v u,¬(H b v u↔H' b v u)→DS.Adj (Sum.inl v) (Sum.inr u))
    (hrim:∀ x,(DR.degree x:ℝ)≤deltaR)
    (hrow:∀ x,(DS.degree (Sum.inl x):ℝ)≤deltaV)
    (hcol:∀ u,(DS.degree (Sum.inr u):ℝ)≤deltaU):
    MarkedRowsWithSpokes P π d h A p k q s g j (errR+h*(deltaR+deltaU)) τ H' ∧
    MarkedIndicesWithSpokes π d h B q s g j (errI+h*deltaV) τ H':=by
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
  have hi':=markedIndices_rim_changes π d h B q s g j errI σ τ H hi
  have hi'':=markedIndices_spoke_relation_changes π d h B q s g j errI deltaV hV τ H H' hi' (by
    intro a x
    calc
      _ ≤∑ u:U,if ¬(H a x u↔H' a x u) then (1:ℝ) else 0:=by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
        intro u _ _; split_ifs <;> positivity
      _ ≤ (DS.degree (Sum.inl x):ℝ):=by
        convert hsrow a x using 1
        apply Finset.sum_congr rfl
        intro u _
        unfold bipAdj
        split_ifs <;> simp_all
      _ ≤ deltaV:=hrow x)
  refine ⟨?_,hi''⟩
  convert hr'' using 1 <;> ring

end Oberwolfach
