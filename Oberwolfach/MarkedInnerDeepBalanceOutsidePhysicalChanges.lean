module

public import Oberwolfach.MarkedInnerDeepBalanceFullyLocalizedTransfer
public import Oberwolfach.MarkedTwoRestrictedDegreesOutside
public import Oberwolfach.MarkedInnerBalanceProtectedCorrection
public import Oberwolfach.MarkedDeeperProtectedRootsZero

@[expose] public section
/-! Transfer relative inner balance using localized changes and transfer the
separate deeper balance using an ambient cap. This avoids scaling the ambient
cap by the inner-set size. The outside-root change bounds are explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_inner_deep_balance_from_outside_physical_changes
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (A T:Finset V) (B R:Finset U)
    (etaBal x δR δS:ℝ) (hη:0<etaBal) (hx:0<x) (hR0:0≤δR) (hS0:0≤δS)
    (hTA:T⊆A) (hRB:R⊆B)
    (hlocalBudget:2*δR+((m+2:ℕ):ℝ)*δS≤min ((x/4)*Fintype.card V) ((etaBal/2)*A.card))
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (hTypes:∀v u,¬(H false v u∧H true v u))
    (hTypes':∀v u,¬(H' false v u∧H' true v u))
    (hrim:∀mark v w,v∈A→w∈A→
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark v w=1 ↔
       markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark v w=1))
    (hspoke:∀b v u,v∈A→u∈B→(H b v u↔H' b v u))
    (hπ:∀v,π v∈A↔v∈A) (FR:SimpleGraph V)
    (hRgraph:∀a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈FR.edgeFinset)
    (hFRoutside:∀v,v∉A→(FR.degree v:ℝ)≤δR)
    (hrowOutside:∀v,v∉A→(∑u∈B,if ¬(H false v u↔H' false v u) then (1:ℝ) else 0)≤δS)
    (hmark:∀v u,H true v u↔H' true v u)
    (hnoNew:∀u v,v∈A→H' false v u→H false v u)
    (hloss:∀u,((A.filter (fun v=>H false v u ∧ ¬H' false v u)).card:ℝ)≤δS):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)
    let E':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true
    let S':=Finset.univ.filter (fun s:V×U=>H' false s.1 s.2∨H' true s.1 s.2);
    (∀v j,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m A B v j|≤(x/4)*Fintype.card V)→
    (∀v j,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m A B v j|≤(etaBal/2)*A.card)→
    (∀v j,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m T R v j|≤(x/4)*Fintype.card V)→
    ∃errI errT:ℝ,0≤errT ∧ errI≤(x/2)*Fintype.card V ∧ errT≤(x/2)*Fintype.card V ∧
      (∀v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m A B v j|≤errI) ∧
      (∀v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m T R v j|≤errT) ∧
      (∀v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m A B v j|≤etaBal*A.card) :=by
  have hboth:=marked_two_restricted_degrees_outside P π d A T hπ σ τ FR δR hRgraph hFRoutside
  exact marked_inner_deep_balance_fully_localized_transfer P π d m A T B R etaBal x δR δS hη hx hR0 hS0 hTA hRB hlocalBudget σ τ H H' hTypes hTypes' hrim hspoke
    (fun mark incoming v hv=>(hboth mark incoming v hv).1)
    (fun mark incoming v hv=>(hboth mark incoming v hv).2) hrowOutside hmark hnoNew hloss
end Oberwolfach
