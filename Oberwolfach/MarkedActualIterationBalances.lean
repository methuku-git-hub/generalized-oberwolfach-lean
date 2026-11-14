module

public import Oberwolfach.MarkedIterationBalanceFromResources
public import Oberwolfach.MarkedCanonicalDeletedBalanceValues

@[expose] public section

/-! The actual physically deleted sample satisfies the next restricted
balance bounds. At inner roots the equality is exact; outside roots are
charged only the original protected-star deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_actual_iteration_balances
    (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ) (σ : RawMarkedOutcome V U Γ Color)
    (H : Bool→V→U→Prop) (X : Finset V) (Z : Finset U) (hX : ∀ v,π v∈X↔v∈X)
    (δ sigma eps η : ℝ) (hsigma : 0≤sigma) (heps : 0<eps)
    (hsize : eps*Fintype.card V/2≤X.card) (hmargin : δ+2*(m+2)*sigma/eps≤η) :
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
        (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) e∈R.filter (markedStarResource X Z))).card:ℝ)≤sigma*Fintype.card V)→
    (∀ z i,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m X Z z i|≤δ*X.card)→
    let σ' := rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ KA).edgeFinset
    let H' := markedDeletePhysicalSpokes H (markedFiniteSpokeGraph KS)
    let E' := MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K' := MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let S' := Finset.univ.filter (fun s:V×U=>H' false s.1 s.2∨H' true s.1 s.2);
    (∀ z i,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m X Z z i|≤η*X.card) ∧
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
  obtain ⟨hnext,hinner,_,_⟩ := marked_iteration_balance_from_resource_bounds
    (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
    π (H false) (H true) Finset.univ KA S KS R m X Z hX (Finset.subset_univ _) hKS
    hA hS hSB hInner δ sigma eps η (Fintype.card V) hsigma (Nat.cast_nonneg _)
    heps hsize hmargin hInc hBal
  constructor
  · intro z i
    rw [(marked_canonical_deleted_balance_values P π d m σ H KA KS X Z z i).2]
    exact hnext z i
  · intro z hz i
    rw [(marked_canonical_deleted_balance_values P π d m σ H KA KS X Z z i).2]
    exact hinner z hz i

end Oberwolfach
