module

public import Oberwolfach.PrescribedPackingCommonEvent

@[expose] public section
/-! Named version of the original prescribed-inner-edge event; its numerical
and domain hypotheses are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]
def OrdinaryPrescribedInnerEvent (r:ℕ) (P F:SimpleGraph V) (π:Equiv.Perm V)
    (d:ℕ) (α p₀ γ:ℝ) (A:Finset V) (U₀:Finset U) (j:Color)
    (σ:RawWheelOutcome V U Γ Color):Prop :=
∀ (Q:SimpleGraph V) (H:V→U→Prop) (ℓ:ℝ),0≤ℓ →
        6*ℓ≤(p₀^6*γ/4)*A.card → 6*ℓ≤(p₀^6*γ/4)*U₀.card →
        (∀ v,((changed (A∩(rawWheelGraph P σ).neighborFinset v) (A∩Q.neighborFinset v)).card:ℝ)≤ℓ) →
        (∀ v,((changed (U₀∩Finset.univ.filter (rawWheelSpokes π d σ j v))
          (U₀∩Finset.univ.filter (H v))).card:ℝ)≤ℓ) →
        (∀ u∈U₀,((changed (A∩Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v u))
          (A∩Finset.univ.filter (fun v=>H v u))).card:ℝ)≤ℓ) →
    ∀     (I X:Finset V) (J B:Finset U) (hIX:Disjoint I X) (hJB:Disjoint J B)
    (Nr Ns D₀:ℕ)
    (x y:Fin Nr→V) (hx:∀ i,x i∈I) (hy:∀ i,y i∈I)
    (hxy:∀ i,Q.Adj (x i) (y i)) (hFxy:∀ i,¬F.Adj (x i) (y i))
    (hedge:∀ i j,i≠j → ¬((x i=x j∧y i=y j)∨(x i=y j∧y i=x j)))
    (hend:∀ a,(Finset.univ.filter (fun i=>a=x i∨a=y i)).card≤D₀)
    (z:Fin Ns→V) (u:Fin Ns→U) (hz:∀ i,z i∈I) (hu:∀ i,u i∈J) (hH:∀ i,H (z i) (u i))
    (hspoke:Function.Injective (fun i=>(z i,u i)))
    (hsend:∀ a,(Finset.univ.filter (fun i=>a=z i)).card≤D₀)
    (hshub:∀ v,(Finset.univ.filter (fun i=>u i=v)).card≤D₀)
    (hJB0:J∪B⊆U₀)
    (hN:((Nr+Ns:ℕ):ℝ)≤α^2*(A.card:ℝ)^2) (hD:(D₀:ℝ)≤α*A.card)
    (hXA:((A\X).card:ℝ)≤p₀^6*γ*A.card/8)
    (hBU:((U₀\B).card:ℝ)≤p₀^6*γ*U₀.card/8)
,
    ∃ C:(Fin Nr⊕Fin Ns)→OrdinaryWheel Q F H r,
      (∀ i j,i≠j → Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j))) ∧
      (∀ i,ordinaryWheelResources (C i)∩ordinaryHostResources (spanningRestriction Q I)
        (fun a v=>H a v∧a∈I∧v∈J)=
        {Sum.elim (fun j=>Sum.inl s(x j,y j)) (fun j=>Sum.inr (z j,u j)) i}) ∧
      (∀ a,((wheelFamilyRim C).degree a:ℝ)≤12*α*A.card) ∧
      (∀ a,((Finset.univ.filter (fun v=>wheelFamilySpokes C a v)).card:ℝ)≤6*α*A.card) ∧
      (∀ v,((Finset.univ.filter (fun a=>wheelFamilySpokes C a v)).card:ℝ)≤3*α*A.card*r)
end Oberwolfach
