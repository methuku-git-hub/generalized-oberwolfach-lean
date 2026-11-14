module

public import Oberwolfach.MarkedActualInnerCorrectionInputs
public import Oberwolfach.MarkedFiniteCountsFromIncidence
public import Oberwolfach.MarkedCanonicalDeletedBalanceValues

@[expose] public section

/-! The actual physically deleted sample has balance error at most the
original absolute error plus (m+2) times the realised protected-star bound.
At inner roots its balance values are unchanged. No normalization is altered. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_actual_iteration_balance_error
    (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ) (σ : RawMarkedOutcome V U Γ Color)
    (H : Bool→V→U→Prop) (X : Finset V) (Z : Finset U) (hX : ∀ v,π v∈X↔v∈X)
    (err δ : ℝ) (hδ : 0≤δ) :
    let E := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S := Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2);
    ∀ (KA : Finset (E⊕K)) (KS : Finset (V×U)),KS⊆S→
    let R := markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π KA KS;
    R.filter (markedInnerResource X Z)=∅→
    (∀ physical z,(((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) physical z).filter
      (fun e=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) e∈R.filter (markedStarResource X Z))).card:ℝ)≤δ)→
    (∀ z i,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m X Z z i|≤err)→
    let σ' := rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ KA).edgeFinset
    let H' := markedDeletePhysicalSpokes H (markedFiniteSpokeGraph KS)
    let E' := MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K' := MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let S' := Finset.univ.filter (fun s:V×U=>H' false s.1 s.2∨H' true s.1 s.2);
    (∀ z i,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m X Z z i|≤err+(m+2)*δ) ∧
    (∀ z,Sum.elim (fun v=>v∈X) (fun u=>u∈Z) z→∀ i,
      markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m X Z z i=
      markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m X Z z i) := by
  intro E K S KA KS hKS R hInner hInc hBal σ' H' E' K' S'
  have hA : ∀ a∈KA,Sum.inl (markedPhysicalEdge (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π a)∈R := by
    intro a ha
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
  have hS : ∀ s∈KS,H false s.1 s.2∨H true s.1 s.2 :=
    fun s hs=>(Finset.mem_filter.mp (hKS hs)).2
  have hSB : ∀ s∈KS,Sum.inr s∈R := fun s hs=>
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s,hs,rfl⟩)
  obtain ⟨hAr,hSr,hSc,_⟩ := marked_finite_star_counts_from_incidence
    (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
    π (H false) (H true) KA KS R X Z hX δ hA hS hSB hInc
  constructor
  · intro z i
    rw [(marked_canonical_deleted_balance_values P π d m σ H KA KS X Z z i).2,
      markedFiniteDomainBalance_sdiff _ _ _ _ _ Finset.univ KA S KS m X Z (Finset.subset_univ _) hKS]
    have hb := markedFiniteDomainBalance_bound
      (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2) (H true)
      (KA.filter (fun a=>Sum.elim (fun e:E=>e.val.1) (fun e:K=>e.val.1) a∈X ∨
        Sum.elim (fun e:E=>e.val.2) (fun e:K=>e.val.2) a∈X))
      (KS.filter (fun s=>s.1∈X∨s.2∈Z)) m X Z δ hδ hAr hSr hSc z i
    rw [markedFiniteDomainBalance_star] at hb
    exact (abs_sub _ _).trans (add_le_add (hBal z i) hb)
  · exact marked_actual_inner_balance_unchanged P π d m σ H X Z hX KA KS hKS hInner

end Oberwolfach
