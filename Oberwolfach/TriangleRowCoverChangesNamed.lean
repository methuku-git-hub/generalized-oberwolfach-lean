module

public import Oberwolfach.TriangleRowCoverChangesCommonEvent

@[expose] public section
/-! Name the same robust triangle row event for modular same-sample use. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V Γ Color:Type} [Fintype V] [Fintype Γ] [Fintype Color] [DecidableEq V]

def TriangleRowCoverChangesEvent (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (A B X Y:Finset V) (hYB:Disjoint Y B) (pR pH η θ ρ:ℝ)
    (j:Color) (σ:RawWheelOutcome V V Γ Color):Prop :=
    let R:=rawWheelGraph P σ\F
    let H:=bipartiteRelationGraph Y B hYB (rawWheelSpokes π d σ j)
    ∀ (Q J:SimpleGraph V) (L:ℝ),0≤L → L≤ρ*A.card → Q≤P\F →
      (∀v,(F.degree v:ℝ)≤L) →
      (∀v,((changed (A∩R.neighborFinset v) (A∩Q.neighborFinset v)).card:ℝ)≤L) →
      (∀v,((changed (B∩H.neighborFinset v) (B∩J.neighborFinset v)).card:ℝ)≤L) →
      (∀u∈B,((changed (A∩H.neighborFinset u) (A∩J.neighborFinset u)).card:ℝ)≤L) →
      (∀v,((R\Q).degree v:ℝ)≤L) → (∀v,((Q\R).degree v:ℝ)≤L) →
      (∀v,((H\J).degree v:ℝ)≤L) → (∀v,((J\H).degree v:ℝ)≤L) →
      (∀a∈Y,J.neighborFinset a⊆B) →
    ∀ (Z:Finset V),Z⊆A → ∀ (n:ℕ) (x:Fin n→V),
      (n:ℝ)≤θ*A.card → Function.Injective x → (∀ i,x i∈X) → (∀ i,x i∉Z) →
      (∀ i,Q.neighborFinset (x i)⊆Z) →
      (∀ i,|pR*(A∩P.neighborFinset (x i)).card/(2*B.card*pH)-1|≤η) →
      (∀ i,Q.degree (x i)=2*J.degree (x i)) →
      ∃ M:Fin n→Finset (OrdinaryWheel Q F J.Adj 3),
        (∀ i,OrdinaryRowCover (M i) (x i) Z 0) ∧
        (∀ i j,i≠j → Disjoint ((M i).biUnion ordinaryWheelResources) ((M j).biUnion ordinaryWheelResources)) ∧
        (∀ i,∀ W∈M i,∀ k,x k∈(ordinaryWheelRim W).support ↔ k=i) ∧
        (∀ a∈Z,(ordinaryWheelRimGraph (Finset.univ.biUnion M)).degree a≤2*n) ∧
        (∀ a∈Z,(Finset.univ.filter (ordinaryPackingSpokes (Finset.univ.biUnion M) a)).card≤n) ∧
        (∀ u,(Finset.univ.filter (fun a=>ordinaryPackingSpokes (Finset.univ.biUnion M) a u )).card≤3*n)
end Oberwolfach
