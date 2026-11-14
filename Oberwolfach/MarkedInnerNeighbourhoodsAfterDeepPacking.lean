module

public import Oberwolfach.MarkedInnerDeletionBudgets
public import Oberwolfach.MarkedNeighbourhoodPhysicalDeletion
public import Oberwolfach.MarkedPhysicalDeletionComposition

@[expose] public section

/-! Deep wheels avoiding the inner star change neither inner row tests nor
inner index tests, including those with ambient roots outside the inner
sets. Only the prescribed-edge packing contributes an error. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_neighbourhoods_star_avoiding_deletion
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (A:Finset V) (B:Finset U)
    (hA:∀ x,π x∈A↔x∈A)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (errR errI:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hr:MarkedRowsWithSpokes P π d h A p k q s g j errR σ H)
    (hi:MarkedIndicesWithSpokes π d h B q s g j errI σ H)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hR:∀ x,∀ y∈A,¬DR.Adj x y)
    (hSrow:∀ x∈A,∀ u,¬DS.Adj (Sum.inl x) (Sum.inr u))
    (hScol:∀ u∈B,∀ x,¬DS.Adj (Sum.inl x) (Sum.inr u)):
    MarkedRowsWithSpokes P π d h A p k q s g j errR
      (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS)∧
    MarkedIndicesWithSpokes π d h B q s g j errI
      (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS):=by
  have hphys (a:Bool×Bool×V) (x:V) (hx:x∈A):
      markedPairPhysical π (markedRowRim a x)∉DR.edgeFinset:=by
    rcases a with ⟨mark,incoming,v⟩
    cases mark <;> cases incoming <;>
      simp only [markedPairPhysical,markedRowRim,Bool.false_eq_true,ite_false,ite_true,Sum.elim_inl,Sum.elim_inr,
        SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
    · exact hR v x hx
    · exact fun he=>hR v x hx he.symm
    · exact hR v (π x) ((hA x).mpr hx)
    · exact fun he=>hR (π v) x hx he.symm
  have hrim:=markedRows_rim_changes P π d h A p k q s g j errR 0 (by norm_num) σ
    (rawMarkedDeleteRims σ DR.edgeFinset) H hr (by
      intro a
      have he:∀ x∈A,(if ¬(rawMarkedPairRims P π d σ (markedRowRim a x)↔
          rawMarkedPairRims P π d (rawMarkedDeleteRims σ DR.edgeFinset) (markedRowRim a x)) then (1:ℝ) else 0)=0:=by
        intro x hx
        simp only [rawMarkedDeleteRims_rims,hphys a x hx,not_false_eq_true,and_true,iff_self,not_true_eq_false,ite_false]
      simp only [Finset.sum_congr rfl he,Finset.sum_const_zero,le_refl])
  simp only [mul_zero,add_zero] at hrim
  have hrows:=markedRows_spoke_relation_changes P π d h A p k q s g j errR 0 (by norm_num)
    (rawMarkedDeleteRims σ DR.edgeFinset) H (markedDeletePhysicalSpokes H DS) hrim (by
      intro mark u
      have he:∀ x∈A,(if ¬(H mark x u↔markedDeletePhysicalSpokes H DS mark x u) then (1:ℝ) else 0)=0:=by
        intro x hx;simp [markedDeletePhysicalSpokes,hSrow x hx u]
      simp only [Finset.sum_congr rfl he,Finset.sum_const_zero,le_refl])
  have hidx:=markedIndices_spoke_relation_changes π d h B q s g j errI 0 (by norm_num)
    (rawMarkedDeleteRims σ DR.edgeFinset) H (markedDeletePhysicalSpokes H DS)
    (markedIndices_rim_changes π d h B q s g j errI σ _ H hi) (by
      intro mark x
      have he:∀ u∈B,(if ¬(H mark x u↔markedDeletePhysicalSpokes H DS mark x u) then (1:ℝ) else 0)=0:=by
        intro u hu;simp [markedDeletePhysicalSpokes,hScol u hu x]
      simp only [Finset.sum_congr rfl he,Finset.sum_const_zero,le_refl])
  simpa only [mul_zero,add_zero] using And.intro hrows hidx

variable {E K:Type} {tail head:E→V} {ktail khead:K→V} {π₀:Equiv.Perm V} {m₀ b₀:ℕ} {H₀ HK:V→U→Prop}

theorem marked_inner_neighbourhoods_after_both_packings
    (MD:Finset (MarkedWheel tail head ktail khead m₀ π₀ b₀ H₀ HK)) (A:Finset V) (B:Finset U)
    (hstar:(MD.biUnion markedWheelPhysicalResources).filter (markedStarResource A B)=∅)
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (hA:∀ x,π x∈A↔x∈A)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color)
    (errR errI δR δV δU:ℝ) (hdR:0≤δR) (hdV:0≤δV) (hdU:0≤δU)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hr:MarkedRowsWithSpokes P π d h A p k q s g j errR σ H)
    (hi:MarkedIndicesWithSpokes π d h B q s g j errI σ H)
    (ER:SimpleGraph V) (ES:SimpleGraph (V⊕U))
    (hrim:∀ x,(ER.degree x:ℝ)≤δR) (hrow:∀ x,(ES.degree (Sum.inl x):ℝ)≤δV)
    (hcol:∀ u,(ES.degree (Sum.inr u):ℝ)≤δU):
    MarkedRowsWithSpokes P π d h A p k q s g j (errR+h*(δR+δU))
      (rawMarkedDeleteRims σ (ER⊔markedPackingRimGraph MD).edgeFinset)
      (markedDeletePhysicalSpokes H (ES⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)))∧
    MarkedIndicesWithSpokes π d h B q s g j (errI+h*δV)
      (rawMarkedDeleteRims σ (ER⊔markedPackingRimGraph MD).edgeFinset)
      (markedDeletePhysicalSpokes H (ES⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs))):=by
  obtain ⟨hrowE,hidxE⟩:=marked_neighbourhoods_after_physical_deletion P π d h A B p k q s g j
    errR errI δR δV δU hdR hdV hdU σ H hr hi ER ES hrim hrow hcol
  have hs:=marked_deep_spoke_graph_avoids_inner MD A B hstar
  have hR:∀ x,∀ y∈A,¬(markedPackingRimGraph MD).Adj x y:=by
    intro x y hy hxy
    have hm:=Finset.mem_inter.mpr ⟨((markedPackingRimGraph MD).mem_neighborFinset x y).mpr hxy,hy⟩
    rw [(marked_packing_star_avoidance_neighbours MD A B hstar).1 x] at hm
    exact Finset.notMem_empty y hm
  have hafter:=marked_neighbourhoods_star_avoiding_deletion P π d h A B hA p k q s g j _ _
    (rawMarkedDeleteRims σ ER.edgeFinset) (markedDeletePhysicalSpokes H ES) hrowE hidxE
    (markedPackingRimGraph MD) (markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)) hR
    (fun x hx u he=>hs.1 (Sum.inr u) x hx he.symm) (fun u hu x=>hs.2 (Sum.inl x) u hu)
  simpa only [rawMarkedDeleteRims_sup,markedDeletePhysicalSpokes_sup] using hafter

end Oberwolfach
