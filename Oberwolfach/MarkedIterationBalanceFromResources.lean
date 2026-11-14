module

public import Oberwolfach.MarkedFiniteCountsFromIncidence
public import Oberwolfach.MarkedIterationBalancePreservation

@[expose] public section

/-! The actual protected-star output supplies the next level's restricted
balance bounds. The unchanged inner resource set gives exact inheritance
at inner roots, while outside roots incur the stated star-degree loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K : Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_iteration_balance_from_resource_bounds
    (tail head : E→V) (ktail khead : K→V) (π : Equiv.Perm V) (H₀ HK : V→U→Prop)
    (A EA : Finset (E⊕K)) (S ES : Finset (V×U)) (B : Finset (Finset V⊕(V×U)))
    (m : ℕ) (X : Finset V) (Z : Finset U) (hX : ∀ v,π v∈X↔v∈X)
    (hEA : EA⊆A) (hES : ES⊆S)
    (hA : ∀ a∈EA,Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈B)
    (hS : ∀ s∈ES,H₀ s.1 s.2 ∨ HK s.1 s.2) (hSB : ∀ s∈ES,Sum.inr s∈B)
    (hInner : B.filter (markedInnerResource X Z)=∅)
    (δ σ ε η n : ℝ) (hσ : 0≤σ) (hn : 0≤n) (hε : 0<ε)
    (hsize : ε*n/2≤X.card) (hmargin : δ+2*(m+2)*σ/ε≤η)
    (hB : ∀ physical z,(((markedIncidentEdges tail head ktail khead π H₀ HK physical z).filter
      (fun e=>markedActivePhysical tail head ktail khead π H₀ HK e∈B.filter (markedStarResource X Z))).card : ℝ)≤σ*n)
    (hBal : ∀ z i,|markedFiniteDomainBalance tail head ktail khead HK A S m X Z z i|≤δ*X.card) :
    (∀ z i,|markedFiniteDomainBalance tail head ktail khead HK (A\EA) (S\ES) m X Z z i|≤η*X.card) ∧
    (∀ z,Sum.elim (fun v=>v∈X) (fun u=>u∈Z) z→∀ i,
      markedFiniteDomainBalance tail head ktail khead HK (A\EA) (S\ES) m X Z z i=
        markedFiniteDomainBalance tail head ktail khead HK A S m X Z z i) ∧
    (A\EA).filter (fun a=>Sum.elim tail ktail a∈X ∧ Sum.elim head khead a∈X)=
      A.filter (fun a=>Sum.elim tail ktail a∈X ∧ Sum.elim head khead a∈X) ∧
    (S\ES).filter (fun s=>s.1∈X ∧ s.2∈Z)=S.filter (fun s=>s.1∈X ∧ s.2∈Z) := by
  obtain ⟨hAr,hSr,hSc,_⟩ := marked_finite_star_counts_from_incidence tail head ktail khead π H₀ HK EA ES B X Z hX (σ*n)
    hA hS hSB hB
  have hInnerA : EA.filter (fun a=>Sum.elim tail ktail a∈X ∧ Sum.elim head khead a∈X)=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro a ha hin
    have he : Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈B.filter (markedInnerResource X Z) := by
      apply Finset.mem_filter.mpr
      refine ⟨hA a ha,?_⟩
      exact (marked_physical_edge_inner_iff X hX a).mpr hin
    rw [hInner] at he
    exact Finset.notMem_empty _ he
  have hInnerS : ES.filter (fun s=>s.1∈X ∧ s.2∈Z)=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro s hs hin
    have he : Sum.inr s∈B.filter (markedInnerResource X Z) := Finset.mem_filter.mpr ⟨hSB s hs,hin⟩
    rw [hInner] at he
    exact Finset.notMem_empty _ he
  obtain ⟨hnext,hinner,hArcs,hSpokes⟩ := marked_iteration_restricted_balance_preservation tail head ktail khead HK
    A EA S ES m X Z hEA hES hInnerA hInnerS (σ*n) (δ*X.card) (mul_nonneg hσ hn) hAr hSr hSc hBal
  have hnorm := marked_iteration_balance_normalized m δ σ ε η n X.card hε hn hsize hmargin hσ
  refine ⟨?_,hinner,hArcs,hSpokes⟩
  intro z i
  exact (hnext z i).trans (by nlinarith only [hnorm])

end Oberwolfach
