module

public import Oberwolfach.OrdinaryDeepCoverFiniteSeparateLoad

@[expose] public section
/-! Name the uniformly robust ordinary deep-cover event without changing any
    of its original host, perturbation or rooted packing assumptions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def OrdinaryDeepCoverSeparateLoadEvent (m K:ℕ) (a aLoad ρ θ:ℝ) (P F:SimpleGraph V) (J:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color):Prop :=
  ∀ (Q:SimpleGraph V) (H:V→U→Prop) (L:ℝ),Q≤P → 0≤L → L≤ρ*Fintype.card V →
        (∀ v,(F.degree v:ℝ)≤L) →
        (∀ v,((changed ((rawWheelGraph P σ).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L) →
        (∀ v,((changed (Finset.univ.filter (rawWheelSpokes π d σ j v)) (Finset.univ.filter (H v))).card:ℝ)≤L) →
        (∀ u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v u))
          (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L) →
      ∀ I:Finset V,(I.card:ℝ)≤a*Fintype.card V →
      ∀ (E:Finset (Sym2 V⊕(V×U))) (D₀:ℕ),
        E⊆ordinaryHostResources (spanningRestriction Q I) (fun v u=>H v u∧v∈I∧u∈J) →
        (∀ v w,Sum.inl s(v,w)∈E→¬F.Adj v w) →
        (∀ t,(E.filter (ordinaryResourceIncident t)).card≤D₀) →
        (E.card:ℝ)≤aLoad^2*(Fintype.card V:ℝ)^2 → (D₀:ℝ)≤aLoad*Fintype.card V →
      ∀ (T:Finset V) (W:Finset U),T⊆I → W⊆J →
        (T.card:ℝ)≤θ*Fintype.card V → (2*W.card:ℝ)≤L →
        (∀ u∈W,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card) →
        (∀ v∈T,∀ w,Q.Adj v w→¬F.Adj v w) →
        (∀ v∈T,Q.degree v=2*(Finset.univ.filter (H v)).card) →
        (∀ v∈T,∀ w∈I,Q.Adj v w→Sum.inl s(v,w)∈E) →
        (∀ v∈T,∀ u∈J,H v u→Sum.inr (v,u)∈E) →
        (∀ u∈W,∀ v∈I,H v u→Sum.inr (v,u)∈E) →
      ∃ PE:Finset (OrdinaryWheel Q F H (m+1)),
        (∀ A∈PE,∀ B∈PE,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B)) ∧
        PE.biUnion ordinaryWheelResources∩ordinaryHostResources (spanningRestriction Q I)
          (fun v u=>H v u∧v∈I∧u∈J)=E ∧
        (∀ Y∈PE,(ordinaryWheelResources Y∩E).card=1) ∧
        (∀ v,((ordinaryWheelRimGraph PE).degree v:ℝ)≤12*aLoad*Fintype.card V) ∧
        (∀ v,((Finset.univ.filter (ordinaryPackingSpokes PE v)).card:ℝ)≤6*aLoad*Fintype.card V) ∧
        (∀ u,((Finset.univ.filter (fun v=>ordinaryPackingSpokes PE v u)).card:ℝ)≤3*aLoad*Fintype.card V*(m+1)) ∧
      ∃ M:Finset (OrdinaryWheel (Q\ordinaryWheelRimGraph PE) F
          (fun v u=>H v u∧¬ordinaryPackingSpokes PE v u) (m+1)),
        (∀ A∈M,∀ B∈M,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B)) ∧
        (∀ v∈T,∀ w,(ordinaryWheelRimGraph M).Adj v w↔(Q\ordinaryWheelRimGraph PE).Adj v w) ∧
        (∀ v∈T,∀ u,ordinaryPackingSpokes M v u↔H v u∧¬ordinaryPackingSpokes PE v u) ∧
        (∀ u∈W,∀ v,ordinaryPackingSpokes M v u↔H v u∧¬ordinaryPackingSpokes PE v u) ∧
        (∀ v∉I,(ordinaryWheelRimGraph M).degree v≤2*W.card+T.card*(2*(K+1))) ∧
        (∀ v∉I,(Finset.univ.filter (ordinaryPackingSpokes M v)).card≤W.card+T.card*(K+1)) ∧
        (∀ u∉J,(Finset.univ.filter (fun v=>ordinaryPackingSpokes M v u)).card≤T.card*(m+1)) ∧
        (∀ Y∈M,(ordinaryWheelVertices Y∩(T.image Sum.inl∪W.image Sum.inr)).card=1) ∧
        (∀ v∈I\T,∀ w,¬(ordinaryWheelRimGraph M).Adj v w) ∧
        (∀ v∈I\T,∀ u,¬ordinaryPackingSpokes M v u) ∧
        (∀ u∈J\W,∀ v,¬ordinaryPackingSpokes M v u) ∧
      ∃ P':Finset (OrdinaryWheel Q F H (m+1)),
        (∀ A∈P',∀ B∈P',A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B)) ∧
        P'.biUnion ordinaryWheelResources∩ordinaryHostResources (spanningRestriction Q I)
          (fun v u=>H v u∧v∈I∧u∈J)=E ∧
        (∀ v∈T,∀ w,(ordinaryWheelRimGraph P').Adj v w↔Q.Adj v w) ∧
        (∀ v∈T,∀ u,ordinaryPackingSpokes P' v u↔H v u) ∧
        (∀ u∈W,∀ v,ordinaryPackingSpokes P' v u↔H v u)
end Oberwolfach
