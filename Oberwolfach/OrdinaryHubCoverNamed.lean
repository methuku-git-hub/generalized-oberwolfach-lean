module

public import Oberwolfach.OrdinaryHubCoverCommonEvent

@[expose] public section
/-! Name the robust hub-cover event on its original raw sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def OrdinaryHubCoverEvent (m:ℕ) (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (ρ:ℝ)
    (j:Color) (σ:RawWheelOutcome V U Γ Color):Prop :=
      let R:=rawWheelGraph P σ
      let H:=rawWheelSpokes π d σ j
    ∀ (Q:SimpleGraph V) (H':V→U→Prop) (L:ℝ),Q≤P → 0≤L → L≤ρ*Fintype.card V →
      (∀ v,(F.degree v:ℝ)≤L) →
      (∀ v,((changed (R.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L) →
      (∀ v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (H' v))).card:ℝ)≤L) →
      (∀ u,((changed (Finset.univ.filter (fun v=>H v u)) (Finset.univ.filter (fun v=>H' v u))).card:ℝ)≤L) →
    ∀ (n:ℕ) (u:Fin n→U),Function.Injective u →
      (∀ v,(2*(Finset.univ.filter (fun i=>H' v (u i))).card:ℝ)≤ρ*Fintype.card V) →
      (∀ i,(m+1)∣(Finset.univ.filter (fun v=>H' v (u i))).card) →
      ∃ M:Finset (OrdinaryWheel Q F H' (m+1)),
        (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)) ∧
        M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
          Finset.univ.biUnion (fun i=>(Finset.univ.filter (fun v=>H' v (u i))).image (fun v=>Sum.inr (v,u i))) ∧
        (∀ v,(ordinaryWheelRimGraph M).degree v≤2*(Finset.univ.filter (fun i=>H' v (u i))).card) ∧
        (∀ i,∀ v,H' v (u i)→∃! W:M,Sum.inr (v,u i)∈ordinaryWheelResources W.val)
end Oberwolfach
