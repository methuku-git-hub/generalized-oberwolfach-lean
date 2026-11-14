module

public import Oberwolfach.OrdinaryAdaptiveHubWeightsFromTrace
public import Oberwolfach.OrdinaryVortexTraceBalanceCanonicalCap

@[expose] public section
/-! Apply the universal hub event to the actual protected trace of the
selected raw sample; the host containment follows from physical deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_sample_trace_adaptive_hub_weights
    (P F JQ G:SimpleGraph V) (JH Hs:V→U→Prop) (π:Equiv.Perm V) (d m:ℕ)
    (σ:RawWheelOutcome V U Γ Color) (j:Color) (K:Finset (Sym2 V⊕(V×U)))
    (X T:ℕ→Finset V) (Z W:ℕ→Finset U) (cost deepCost:ℕ→ℝ)
    (n:ℕ) (A:Finset (Sym2 V⊕(V×U)))
    (Wv Wu:Type) [Fintype Wv] [Fintype Wu] [LinearOrder Wv] [DecidableEq Wu]
    (f:Wv↪V) (g:Wu↪U) (ρ:Equiv.Perm Wv) (I:Finset Wv) (B:Finset Wu)
    (pR pH density tR tH L βe βh b Bweight η:ℝ) (s:Wu→Color→ℝ)
    (htrace:let R:=rawWheelGraph P σ; let J:=rawWheelSpokes π d σ j;
     let S:=(R\F)\JQ; let H:=fun v u=>J v u∧¬JH v u;
     let S₀:=S\ordinaryResourceRim S K; let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K);
     OrdinaryProtectedTrace S₀ H₀ X T Z W cost deepCost n A):
    ordinaryHostResources G Hs=A→
    OrdinaryAdaptiveHubWeightsLevelEvent m (P.comap f) (F.comap f) I B ρ d pR pH density tR tH L βe βh b Bweight η s j
      (ordinaryRawRestrictPair f g σ)→
    OrdinaryCleanupParentProfiles (P.comap f) (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u))
      ρ d I B pR pH density tR tH L βe βh s j (ordinaryRawRestrictPair f g σ)→
    Nonempty (OrdinaryMixedHubWeightsOfLength m b Bweight η (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u)) I B):=by
  intro hstate hevent hprofile
  let R:=rawWheelGraph P σ
  let J:=rawWheelSpokes π d σ j
  let S:=(R\F)\JQ
  let H:=fun v u=>J v u∧¬JH v u
  let S₀:=S\ordinaryResourceRim S K
  let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K)
  have hS₀:S₀≤P:=by
    exact (show S₀≤S from sdiff_le).trans ((show S≤R from sdiff_le.trans sdiff_le).trans (retainedGraph_le P _))
  exact ordinary_adaptive_hub_weights_from_protected_trace P S₀ G H₀ Hs X T Z W cost deepCost n A
    htrace hstate hS₀ f g (F.comap f) I B ρ d m pR pH density tR tH L βe βh b Bweight η s j
    (ordinaryRawRestrictPair f g σ) hevent hprofile
end Oberwolfach
