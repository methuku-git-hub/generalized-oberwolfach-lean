module

public import Oberwolfach.OrdinaryTriangleNormalizedMixedSelection
public import Oberwolfach.FiniteLawIntersectionLower
public import Oberwolfach.FixedDomainQuadraticEvent

@[expose] public section
/-! Combine hub and endpoint factor events on the same sample; no
independence between those two events is required. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_normalized_mixed_probability
    (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ):∃N:ℕ,
    ∀(V U K:Type) [Fintype V] [Fintype U] [Fintype K]
      [DecidableEq V] [DecidableEq U] [DecidableEq K]
      (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
      (P B:SimpleGraph (V⊕U)) (S T:K→Finset (V⊕U))
      (g:K→(V⊕U)↪Sym2 (V⊕U)) (hST:∀k,Disjoint (S k) (T k))
      (ζh ζe:ℝ) (n:ℕ),
    N≤A.card→A.card≤n→
    (spanningRestriction Q A).map (Function.Embedding.inl:V↪V⊕U)≤P→
    let μ:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-1/(A.card:ℝ)^(q+1)≤μ.probability (OrdinaryNormalizedHubFactorEvent 2 Q F H A Z p ζh)→
    1-1/(n:ℝ)^(q+1)≤μ.probability (EndpointTriangleNormalizedFactorEvent P B S T g p ζe)→
    1-1/(A.card:ℝ)^q≤μ.probability
      (MixedFreshBoundaryAvoidingEvent p (2*p) (min ζh ζe) (spanningRestriction Q A) F P B
        (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H Z A) S T
        (fun j=>hubSpokeCoin j.val) g hST):=by
  obtain ⟨Ns,hNs⟩:=ordinary_triangle_normalized_mixed_selection (2*p) (by positivity)
  refine ⟨max 2 Ns,?_⟩
  intro V U K _ _ _ _ _ _ Q F H A Z P B S T g hST ζh ζe n hn hnsize hQ μ hhub hend
  have hA:0<A.card:=by omega
  have hAr:0<(A.card:ℝ):=Nat.cast_pos.mpr hA
  have hAn:A.card≤Fintype.card V:=Finset.card_le_univ A
  have hfrac:1/(n:ℝ)^(q+1)≤1/(A.card:ℝ)^(q+1):=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hAr _) (pow_le_pow_left₀ hAr.le (Nat.cast_le.mpr hnsize) _)
  have hi:=finiteLaw_good_intersection μ (OrdinaryNormalizedHubFactorEvent 2 Q F H A Z p ζh)
    (EndpointTriangleNormalizedFactorEvent P B S T g p ζe) (1/(n:ℝ)^(q+1)) hend
  have hb:=scaled_inverse_power_le A.card q hA 2 (by exact_mod_cast (show 2≤A.card by omega))
  have hb':2*(1/(A.card:ℝ)^(q+1))≤1/(A.card:ℝ)^q:=by convert hb using 1 <;> ring
  have hjoint:1-1/(A.card:ℝ)^q≤μ.probability
      (fun σ=>OrdinaryNormalizedHubFactorEvent 2 Q F H A Z p ζh σ ∧
        EndpointTriangleNormalizedFactorEvent P B S T g p ζe σ):=by linarith only [hhub,hi,hfrac,hb']
  apply hjoint.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  exact hNs V U K Q F H A Z P B S T g hST p ζh ζe hp.le σ (by omega) hQ hσ.1 hσ.2
end Oberwolfach
