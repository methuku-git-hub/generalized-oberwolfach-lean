module

public import Oberwolfach.OrdinaryAsymmetricMixedPairingFromEvents
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! Intersect the inner-scale hub and endpoint events on one physical
sample and select their pairings together. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_asymmetric_mixed_pairing_same_sample
    (m:ℕ) (ρ:ℝ) (hρ:0<ρ):∃N:ℕ,
    ∀(V U K:Type) [Fintype V] [Fintype U] [Fintype K] [DecidableEq V] [DecidableEq U] [DecidableEq K],
    N≤Fintype.card (V⊕U)→∀(Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
      (P B:SimpleGraph (V⊕U)) (T:Finset (V⊕U)) (S R:K→Finset (V⊕U)) (g:K→(V⊕U)↪Sym2 (V⊕U))
      (p ζh ζlocal:ℝ) (hp:0<p) (hp1:p≤1)
      (hmap:(spanningRestriction Q A).map (Function.Embedding.inl:V↪V⊕U)≤P)
      (lossH lossE:ℝ),
    let μ:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-lossH≤μ.probability (OrdinaryNormalizedHubFactorEvent m Q F H A Z p ζh)→
    1-lossE≤μ.probability (OrdinaryLocalEndpointEvent P B T S R g p ζlocal)→
    1-lossH-lossE≤μ.probability
      (MixedFreshPairingAsymmetricEvent m p ρ ζh ζlocal T.card (spanningRestriction Q A) F P B
        (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H Z A) S R
        (fun j=>hubSpokeCoin j.val) g):=by
  obtain ⟨N,hN⟩:=ordinary_asymmetric_mixed_pairing_from_events m ρ hρ
  refine ⟨N,?_⟩
  intro V U K _ _ _ _ _ _ hn Q F H A Z P B T S R g p ζh ζlocal hp hp1 hmap
    lossH lossE μ hH hE
  have hi:=finiteLaw_intersection_lower μ
    (OrdinaryNormalizedHubFactorEvent m Q F H A Z p ζh)
    (OrdinaryLocalEndpointEvent P B T S R g p ζlocal) lossH lossE hH hE
  apply hi.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  exact hN V U K hn Q F H A Z P B T S R g p ζh ζlocal hp.le hmap σ hσ.1 hσ.2
end Oberwolfach
