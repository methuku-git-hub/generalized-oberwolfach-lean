module

public import Oberwolfach.MarkedFinitePhysicalIncidenceBound
public import Oberwolfach.MarkedFiniteDomainBalanceBounds
public import Oberwolfach.MarkedInnerDeletionBudgets
public import Oberwolfach.MarkedMatrixDivisibility

@[expose] public section

/-! The prescribed packing's physical rim, spoke-row and spoke-column
degree bounds imply its opposite-endpoint balance bound on every fixed
pair of domains. No small global degree of the deep packing is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem markedPacking_finite_spoke_incidence_counts
    {E K:Type} {tail head:E→V} {ktail khead:K→V} {m b:ℕ}
    {π:Equiv.Perm V} {H₀ HK:V→U→Prop}
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK)):
    (∀ v,((M.biUnion markedWheelSpokePairs).filter (fun s=>s.1=v)).card=
      (Finset.univ.filter (markedPackingSpokes M v)).card)∧
    (∀ u,((M.biUnion markedWheelSpokePairs).filter (fun s=>s.2=u)).card=
      (Finset.univ.filter (fun v=>markedPackingSpokes M v u)).card):=by
  have hm (s:V×U):s∈M.biUnion markedWheelSpokePairs↔markedPackingSpokes M s.1 s.2:=by
    rw [←markedFiniteSpokeGraph_adj,markedFiniteSpokeGraph_packing_adj]
  constructor
  · intro v
    have he:((M.biUnion markedWheelSpokePairs).filter (fun s=>s.1=v))=
        Finset.univ.filter (fun s:V×U=>markedPackingSpokes M s.1 s.2∧s.1=v):=by
      ext s;simp only [Finset.mem_filter,Finset.mem_univ,true_and,hm]
    rw [he]
    exact finite_relation_row_card (markedPackingSpokes M) v
  · intro u
    have he:((M.biUnion markedWheelSpokePairs).filter (fun s=>s.2=u))=
        Finset.univ.filter (fun s:V×U=>markedPackingSpokes M s.1 s.2∧s.2=u):=by
      ext s;simp only [Finset.mem_filter,Finset.mem_univ,true_and,hm]
    rw [he]
    exact finite_relation_col_card (markedPackingSpokes M) u

theorem marked_sample_packing_domain_balance_bound
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop)
    (M:Finset (MarkedWheel
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
      m π (3*d) (H false) (H true)))
    (δR δS:ℝ) (hδR:0≤δR) (hδS:0≤δS)
    (hr:∀ v,((markedPackingRimGraph M).degree v:ℝ)≤δR)
    (hs:∀ v,((Finset.univ.filter (markedPackingSpokes M v)).card:ℝ)≤δS)
    (hc:∀ u,((Finset.univ.filter (fun v=>markedPackingSpokes M v u)).card:ℝ)≤δS)
    (X:Finset V) (Z:Finset U) (z:V⊕U) (i:Fin 4):
    |markedFiniteDomainBalance (fun e=>e.val.1) (fun e=>e.val.2) (fun e=>e.val.1) (fun e=>e.val.2)
      (H true) (M.biUnion markedWheelArcs) (M.biUnion markedWheelSpokePairs) m X Z z i|≤
      (m+2)*(4*δR+δS):=by
  have hR:=marked_finite_physical_incidence_bound P π d σ (M.biUnion markedWheelArcs) δR (by
    rw [markedSampleArcSetGraph_packing];exact hr)
  obtain ⟨hS,hC⟩:=markedPacking_finite_spoke_incidence_counts M
  apply markedFiniteDomainBalance_bound _ _ _ _ _ _ _ _ _ _ (4*δR+δS) (by positivity)
  · intro v;exact (hR v).trans (by linarith)
  · intro v
    rw [hS]
    exact (hs v).trans (by linarith)
  · intro u
    rw [hC]
    exact (hc u).trans (by linarith)

end Oberwolfach
