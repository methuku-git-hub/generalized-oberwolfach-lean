module

public import Oberwolfach.MarkedActualIterationBalanceError
public import Oberwolfach.MarkedResourceDomainMonotonicity
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

theorem marked_nested_iteration_balance_inputs
    (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ) (σ : RawMarkedOutcome V U Γ Color)
    (H : Bool→V→U→Prop) (I T : Finset V) (J Q : Finset U)
    (hI : ∀ v,π v∈I↔v∈I) (hT : ∀ v,π v∈T↔v∈T) (hTI : T⊆I) (hQJ : Q⊆J)
    (errI errT x sigma : ℝ) (hs : 0≤sigma) (hx : 0≤x)
    (hErrI : errI≤(x/2)*Fintype.card V) (hErrT : errT≤(x/2)*Fintype.card V)
    (hscale : (m+2:ℝ)*sigma≤x/4) :
    let E := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S := Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2);
    ∀ (KA : Finset (E⊕K)) (KS : Finset (V×U)),KS⊆S→
    let R := markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π KA KS;
    R.filter (markedInnerResource I J)=∅→
    (∀ physical z,(((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) physical z).filter
      (fun e=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) e∈R.filter (markedStarResource I J))).card:ℝ)
        ≤sigma*Fintype.card V)→
    (∀ z i,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m I J z i|≤errI)→
    (∀ z i,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m T Q z i|≤errT)→
    let σ' := rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ KA).edgeFinset
    let H' := markedDeletePhysicalSpokes H (markedFiniteSpokeGraph KS)
    let E' := MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K' := MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let S' := Finset.univ.filter (fun s:V×U=>H' false s.1 s.2∨H' true s.1 s.2);
    (∀ z i,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m I J z i|≤x*Fintype.card V) ∧
    (∀ z i,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m T Q z i|≤x*Fintype.card V) := by
  intro E K S KA KS hKS R hEmpty hStar hBalI hBalT σ' H' E' K' S'
  have hn : (0:ℝ)≤Fintype.card V := Nat.cast_nonneg _
  have hs' := mul_nonneg hs hn
  have hEmptyT : R.filter (markedInnerResource T Q)=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro e he hin
    have h : e∈R.filter (markedInnerResource I J) :=
      Finset.mem_filter.mpr ⟨he,markedInnerResource_mono hTI hQJ e hin⟩
    rw [hEmpty] at h
    exact Finset.notMem_empty _ h
  have hStarT : ∀ physical z,(((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) physical z).filter
      (fun e=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) e∈R.filter (markedStarResource T Q))).card:ℝ)
        ≤sigma*Fintype.card V := by
    intro physical z
    apply le_trans (b:=(((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) physical z).filter
      (fun e=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) e∈R.filter (markedStarResource I J))).card:ℝ))
    · apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro a ha
      obtain ⟨hi,ha⟩ := Finset.mem_filter.mp ha
      obtain ⟨ha,hin⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨hi,Finset.mem_filter.mpr ⟨ha,markedStarResource_mono hTI hQJ _ hin⟩⟩
    · exact hStar physical z
  have hI' := (marked_actual_iteration_balance_error P π d m σ H I J hI errI (sigma*Fintype.card V)
    hs' KA KS hKS hEmpty hStar hBalI).1
  have hT' := (marked_actual_iteration_balance_error P π d m σ H T Q hT errT (sigma*Fintype.card V)
    hs' KA KS hKS hEmptyT hStarT hBalT).1
  have hBudget (err : ℝ) (he : err≤(x/2)*Fintype.card V) :
      err+(m+2:ℝ)*(sigma*Fintype.card V)≤x*Fintype.card V := by
    nlinarith only [he,mul_le_mul_of_nonneg_right hscale hn,mul_nonneg hx hn]
  exact ⟨fun z i=>(hI' z i).trans (hBudget errI hErrI),fun z i=>(hT' z i).trans (hBudget errT hErrT)⟩

end Oberwolfach
