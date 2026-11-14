module

public import Oberwolfach.MarkedNeighbourhoodPhysicalDeletion
public import Oberwolfach.PhysicalDeletionOnDomain

@[expose] public section

/-! Smaller-domain neighbourhood estimates after deletion. The degree
bounds count neighbours into the fixed domain at every ambient root;
the normalizing row set and the original density functions are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_row_rim_deletion_into_domain
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (σ : RawMarkedOutcome V U Γ Color)
    (D : SimpleGraph V) (A : Finset V) (hA : ∀ x,π x∈A↔x∈A) (δ : ℝ)
    (hD : ∀ x,((D.neighborFinset x∩A).card:ℝ)≤δ) (a : Bool×Bool×V) :
    (∑ x∈A,if ¬(rawMarkedPairRims P π d σ (markedRowRim a x)↔
      rawMarkedPairRims P π d (rawMarkedDeleteRims σ D.edgeFinset) (markedRowRim a x)) then (1:ℝ) else 0)≤δ := by
  have h := physical_deletion_invariant_domain_sum D π A hA δ hD
  have hout (b : Bool) (v : V) : (∑ x∈A,if D.Adj v (optionalSuccessor π b x) then (1:ℝ) else 0)≤δ := by
    have hh := h b v
    rw [Finset.sum_coe_sort A (fun x:V=>if D.Adj v (optionalSuccessor π b x) then (1:ℝ) else 0)] at hh
    exact hh
  calc
    _ ≤ ∑ x∈A,if markedPairPhysical π (markedRowRim a x)∈D.edgeFinset then (1:ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro x hx
      rw [rawMarkedDeleteRims_rims]
      by_cases he : rawMarkedPairRims P π d σ (markedRowRim a x)
      <;> by_cases hd : markedPairPhysical π (markedRowRim a x)∈D.edgeFinset
      <;> simp [he,hd]
    _ ≤ δ := by
      obtain ⟨b,i,v⟩ := a
      cases b <;> cases i
      · simpa only [Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,ite_true,ite_false,markedRowRim,markedPairPhysical,optionalSuccessor,ite_false,Bool.false_eq_true,
          SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hout false v
      · simpa only [Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,ite_true,ite_false,markedRowRim,markedPairPhysical,optionalSuccessor,ite_false,Bool.false_eq_true,
          SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,D.adj_comm] using hout false v
      · simpa only [Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,ite_true,ite_false,markedRowRim,markedPairPhysical,optionalSuccessor,ite_true,
          SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hout true v
      · simpa only [Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,ite_true,ite_false,markedRowRim,markedPairPhysical,optionalSuccessor,ite_true,ite_false,Bool.false_eq_true,
          SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,D.adj_comm] using hout false (π v)

theorem marked_neighbourhoods_after_deletion_on_domain
    (P : SimpleGraph V) (π : Equiv.Perm V) (d h : ℕ) (A : Finset V) (B : Finset U)
    (hA : ∀ x,π x∈A↔x∈A) (p k : ℝ) (q : U→Γ→ℝ) (s : U→Color→ℝ) (g : Γ) (j : Color)
    (errR errI deltaR deltaV deltaU : ℝ) (hR : 0≤deltaR) (hV : 0≤deltaV) (hU : 0≤deltaU)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (hr : MarkedRowsWithSpokes P π d h A p k q s g j errR σ H)
    (hi : MarkedIndicesWithSpokes π d h B q s g j errI σ H)
    (DR : SimpleGraph V) (DS : SimpleGraph (V⊕U))
    (hrim : ∀ x,((DR.neighborFinset x∩A).card:ℝ)≤deltaR)
    (hrow : ∀ x,((B.filter (fun u=>DS.Adj (Sum.inl x) (Sum.inr u))).card:ℝ)≤deltaV)
    (hcol : ∀ u,((A.filter (fun x=>DS.Adj (Sum.inl x) (Sum.inr u))).card:ℝ)≤deltaU) :
    MarkedRowsWithSpokes P π d h A p k q s g j (errR+h*(deltaR+deltaU))
      (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS) ∧
    MarkedIndicesWithSpokes π d h B q s g j (errI+h*deltaV)
      (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS) := by
  have hr' := markedRows_rim_changes P π d h A p k q s g j errR deltaR hR σ _ H hr
    (marked_row_rim_deletion_into_domain P π d σ DR A hA deltaR hrim)
  have hc (b : Bool) (u : U) :
      (∑ x∈A,if ¬(H b x u↔markedDeletePhysicalSpokes H DS b x u) then (1:ℝ) else 0)≤deltaU := by
    calc
      _ ≤ ∑ x∈A,if DS.Adj (Sum.inl x) (Sum.inr u) then (1:ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro x hx
        by_cases hh : H b x u <;> by_cases hd : DS.Adj (Sum.inl x) (Sum.inr u)
        <;> simp [markedDeletePhysicalSpokes,hh,hd]
      _ = ((A.filter (fun x=>DS.Adj (Sum.inl x) (Sum.inr u))).card:ℝ) := by
        simp only [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
      _ ≤ _ := hcol u
  have hr'' := markedRows_spoke_relation_changes P π d h A p k q s g j
    (errR+h*deltaR) deltaU hU (rawMarkedDeleteRims σ DR.edgeFinset) H _ hr' hc
  have hi' := markedIndices_rim_changes π d h B q s g j errI σ (rawMarkedDeleteRims σ DR.edgeFinset) H hi
  have hc' (b : Bool) (x : V) :
      (∑ u∈B,if ¬(H b x u↔markedDeletePhysicalSpokes H DS b x u) then (1:ℝ) else 0)≤deltaV := by
    calc
      _ ≤ ∑ u∈B,if DS.Adj (Sum.inl x) (Sum.inr u) then (1:ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro u hu
        by_cases hh : H b x u <;> by_cases hd : DS.Adj (Sum.inl x) (Sum.inr u)
        <;> simp [markedDeletePhysicalSpokes,hh,hd]
      _ = ((B.filter (fun u=>DS.Adj (Sum.inl x) (Sum.inr u))).card:ℝ) := by
        simp only [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
      _ ≤ _ := hrow x
  have hi'' := markedIndices_spoke_relation_changes π d h B q s g j errI deltaV hV
    (rawMarkedDeleteRims σ DR.edgeFinset) H _ hi' hc'
  refine ⟨?_,hi''⟩
  convert hr'' using 1 <;> ring

end Oberwolfach
