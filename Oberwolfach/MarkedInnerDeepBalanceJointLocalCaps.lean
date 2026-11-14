module

public import Oberwolfach.MarkedJointBalanceBoundaryBudget
public import Oberwolfach.MarkedInnerDeepBalanceOutsidePhysicalChanges
public import Oberwolfach.MarkedLocalizedBalanceOrderedCaps
public import Oberwolfach.MarkedInnerDeepBalanceLocalizedTransfer
public import Oberwolfach.MarkedLocalizedBalanceBudgetChoice

@[expose] public section
/-! Choose the ambient and relative inner caps before the sample. The two
outside-root estimates are still required for the selected correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_inner_deep_balance_joint_local_caps
    (m h:ℕ) (x etaBal:ℝ) (hx:0<x) (hη:0<etaBal):
    ∃c:ℝ,0<c ∧ 2*(h:ℝ)*c≤x/4 ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (A T:Finset V) (B R:Finset U)
      (hTA:T⊆A) (hRB:R⊆B) (hπ:∀v,π v∈A↔v∈A),
    ∀(σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (FR:SimpleGraph V)
    (hTypes:∀v u,¬(H false v u∧H true v u))
    (hTypes':∀v u,¬(H' false v u∧H' true v u))
    (hRgraph:∀a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈FR.edgeFinset)
    (hFRoutside:∀v,v∉A→(FR.degree v:ℝ)≤c*(A.card:ℝ))
    (hrim:∀mark v w,v∈A→w∈A→
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark v w=1 ↔
       markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark v w=1))
    (hspoke:∀b v u,v∈A→u∈B→(H b v u↔H' b v u))
    (hrowOutside:∀v,v∉A→(∑u∈B,if ¬(H false v u↔H' false v u) then (1:ℝ) else 0)≤(c*(A.card:ℝ)))
    (hmark:∀v u,H true v u↔H' true v u)
    (hnoNew:∀u v,v∈A→H' false v u→H false v u)
    (hloss:∀u,((A.filter (fun v=>H false v u ∧ ¬H' false v u)).card:ℝ)≤(c*(A.card:ℝ))),
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
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m A B v j|≤etaBal*A.card)  :=by
  obtain ⟨c,hc,hcost,hchoice⟩:=marked_joint_balance_boundary_budget m h etaBal x hη hx
  refine ⟨c,hc,hcost,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P π d A T B R hTA hRB hπ σ τ H H' FR hTypes hTypes' hRgraph hFRoutside
    hrim hspoke hrowOutside hmark hnoNew hloss E K S E' K' S' hI hIrel hT
  have hδ:0≤c*(A.card:ℝ):=by positivity
  exact marked_inner_deep_balance_from_outside_physical_changes P π d m A T B R etaBal x (c*(A.card:ℝ)) (c*(A.card:ℝ))
    hη hx hδ hδ hTA hRB (hchoice V A) σ τ H H' hTypes hTypes' hrim hspoke hπ FR hRgraph hFRoutside
    hrowOutside hmark hnoNew hloss hI hIrel hT
end Oberwolfach
