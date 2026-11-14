module

public import Oberwolfach.OrdinaryTriangleSameSampleRows

@[expose] public section
/-! Robust triangle row-cover event on the original separate domains. It
allows bounded additions and deletions on the same sampled rim and spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

def OrdinaryTriangleTwoDomainRowEvent (P F:SimpleGraph V) (π:Equiv.Perm V) (d D:ℕ)
    (A X:Finset V) (B:Finset U) (pR pH η θ ρ:ℝ) (j:Color)
    (sample:RawWheelOutcome V U Γ Color):Prop :=
    let R:=rawWheelGraph P sample\F
    let H:=rawWheelSpokes π d sample j;
    ∀ (Q:SimpleGraph V) (J:V→U→Prop) (L:ℝ),0≤L → L+D+2*(3*d:ℕ)≤ρ*A.card → Q≤P\F →
      (∀v,((changed (R.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L) →
      (∀v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (J v))).card:ℝ)≤L) →
      (∀u,((changed (Finset.univ.filter (fun v=>H v u)) (Finset.univ.filter (fun v=>J v u))).card:ℝ)≤L) →
    ∀ (Z:Finset V),Z⊆A → ∀ (n:ℕ) (x:Fin n→V),
      (n:ℝ)≤θ*A.card → Function.Injective x → (∀i,x i∈X) → (∀i,x i∉Z) →
      (∀i,Q.neighborFinset (x i)⊆Z) → (∀i u,J (x i) u→u∈B) →
      (∀i,|pR*(A∩P.neighborFinset (x i)).card/(2*B.card*pH)-1|≤η) →
      (∀i,Q.degree (x i)=2*(Finset.univ.filter (J (x i))).card) →
    ∃ M:Fin n→Finset (OrdinaryWheel Q F J 3),
      (∀i,OrdinaryRowCover (M i) (x i) Z 0) ∧
      (∀i k,i≠k→Disjoint ((M i).biUnion ordinaryWheelResources) ((M k).biUnion ordinaryWheelResources))

theorem ordinary_triangle_augmented_event_implies_two_domain
    (P F:SimpleGraph V) (π:Equiv.Perm V) (σ:Equiv.Perm (V⊕U)) (d D:ℕ)
    (hcomm:∀v,Sum.inl (π v)=σ (Sum.inl v))
    (hF:permutationConflictGraph π (3*d)≤F) (hD:∀v,F.degree v≤D)
    (A X:Finset V) (B:Finset U) (pR pH η θ ρ:ℝ) (j:Color)
    (sample:RawWheelOutcome (V⊕U) (V⊕U) Γ Color):
    let e:V↪V⊕U:=⟨Sum.inl,Sum.inl_injective⟩
    let f:U↪V⊕U:=⟨Sum.inr,Sum.inr_injective⟩
    let P':=P.map e
    let F':=ordinaryTwoDomainConflict F σ (3*d)
    let A':=A.image (Sum.inl:V→V⊕U)
    let B':=ordinarySumHubSet (V:=V) B
    let X':=X.image (Sum.inl:V→V⊕U)
    let Y':=ordinarySumRimSet (V:=V) (U:=U);
    TriangleRowCoverChangesEvent P' F' σ d A' B' X' Y' (ordinary_sum_domains_disjoint B) pR pH η θ ρ j sample →
    OrdinaryTriangleTwoDomainRowEvent P F π d D A X B pR pH η θ ρ j (ordinaryRawRestrictPair e f sample):=by
  intro e f P' F' A' B' X' Y' hBig
  intro Q J L hL hLρ hQ hR hrow hcol Z hZA n x hn hx hX hZ hroot hJ hbalance hbal
  exact ordinary_triangle_same_sample_rows P F Q J π σ d D hcomm hF hD hQ sample j A X Z B n x pR pH η θ ρ L hL hLρ
    hZA hn hx hX hZ hroot hJ hbalance hbal hR hrow hcol hBig
end Oberwolfach
