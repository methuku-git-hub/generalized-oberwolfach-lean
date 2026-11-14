module

public import Oberwolfach.RawMarkedResourceCoordinates

@[expose] public section
/-! Physical changes avoiding the inner pair preserve its typed rims and
spokes, including the permutation in a marked rim's physical head. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_protected_pair_from_change_graphs
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (I:Finset V) (J:Finset U) (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hI:∀ x,x∈I→π x∈I)
    (hRim:∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→
      markedPairPhysical π a∈FR.edgeFinset)
    (hSpoke:∀ b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hFR:∀ x∈I,∀ y∈I,¬FR.Adj x y)
    (hFS:∀ x∈I,∀ u∈J,¬FS.Adj (Sum.inl x) (Sum.inr u)):
    (∀ mark x y,x∈I→y∈I→
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
       markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1)) ∧
    (∀ b v u,v∈I→u∈J→(H b v u↔H' b v u)) :=by
  constructor
  · intro mark x y hx hy
    cases mark with
    | false=>
      change rawMarkedPairRims P π d σ (Sum.inl (x,y)) ↔ rawMarkedPairRims P π d τ (Sum.inl (x,y))
      by_contra hh
      have he:=hRim (Sum.inl (x,y)) hh
      have ha:FR.Adj x y:=by simpa only [markedPairPhysical,Sum.elim_inl,SimpleGraph.mem_edgeSet] using (SimpleGraph.mem_edgeFinset.mp he)
      exact hFR x hx y hy ha
    | true=>
      change rawMarkedPairRims P π d σ (Sum.inr (x,y)) ↔ rawMarkedPairRims P π d τ (Sum.inr (x,y))
      by_contra hh
      have he:=hRim (Sum.inr (x,y)) hh
      have ha:FR.Adj x (π y):=by simpa only [markedPairPhysical,Sum.elim_inr,SimpleGraph.mem_edgeSet] using (SimpleGraph.mem_edgeFinset.mp he)
      exact hFR x hx (π y) (hI y hy) ha
  · intro b v u hv hu
    by_contra hh
    exact hFS v hv u hu (hSpoke b v u hh)
end Oberwolfach
