module

public import Oberwolfach.MarkedParentAndLocalReferenceLoadEvent
public import Oberwolfach.MarkedLocalEstimateMonotonicity
public import Oberwolfach.MarkedPackingFullHubLoads
public import Oberwolfach.MarkedParentAdaptiveLoadEvent
public import Oberwolfach.MarkedPackingAdaptiveVortexEvent
public import Oberwolfach.MarkedPackingZeroDeletionAnyInstance
public import Oberwolfach.RawMarkedPairRestrictionIdentity

@[expose] public section
/-! The one-level specialization of the retained adaptive packing event,
with the full vertex and hub domains and their identity embeddings. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem marked_parent_and_local_reference_load_uniform_density
    (m d:ℕ) (hm:3≤m) (hd:2≤d) (B pstar ε K eta χ Q pret ζ κ θ ω:ℝ)
    (hω:0<ω) (hB:0<B) (hpstar:0<pstar) (hε:0<ε) (hK:1≤K)
    (heta:0<eta) (heta1:eta<1) (hχ:0<χ) (hpret:0<pret) (hζ:0<ζ):
    ∃ N:ℕ,1≤N ∧
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    N≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V),
    (∀ x l,0<l→l<2*d+1→(π^l) x≠x) →
    ∀ (D τ A:ℝ),(Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    τ+ε+11*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*K*ζ≤κ/4 →
    τ+ε+11*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*K*ζ≤θ/4 →
    ∀ weight:(Fin (m+1)→V)→ℝ,SuccessorSequenceWeightConditions P π (3*d) D τ A B weight →
    ∀ (p k s₀:ℝ) (hp:0<p) (hk:0<k) (hphys:2*p+2*k≤1),
    pstar≤p → pstar≤k → pstar≤s₀ → p≤1 → k≤1 → s₀≤1 →
    (Fintype.card U:ℝ)*(s₀/m)=D*k → (Fintype.card U:ℝ)*(s₀/m)*m=D*p →
    ∀ (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (a:Γ) (j:Color),
    (∀ u,q u a=s₀/m) → (∀ u,s u j=s₀) → pret*Fintype.card V≤(s₀/m)*Fintype.card U →
    1-χ-(Fintype.card V:ℝ)^(-Q)≤
      (rawMarkedRetentionLaw π d hd a p k hp.le hk.le hphys q hq hQ s hs hS).probability
      (fun z=>
        let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j;
        let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
          (fun (_:V) (_:U)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m);
        (∀ root,rawMarkedWheelMarginal P π d p k q s a j root≠0 →
          |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d z.1) H root-1|≤κ/4) ∧
        MarkedLocalSpokeLoadsWithSpokes P π d m D p k s₀ weight (θ/4) z.1 H) := by
  obtain ⟨M,N,hM,hN,hbase⟩:=marked_parent_and_local_reference_load_common_event m d hm hd B pstar ε K eta χ Q pret ζ κ θ
    hB hpstar hε hK heta heta1 hχ hpret hζ
  obtain ⟨Nω,hNω⟩:=exists_nat_gt ((M:ℝ)/ω)
  refine ⟨max N Nω,le_trans hN (le_max_left _ _),?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ hn hU hUV P π hnoshort D τ A hDlo hDhi herr herrLocal weight hw p k s₀ hp hk hphys hpp hpk hps hp1 hk1 hs1 hmarked hord q hq hQ s hs hS a j ha hj hmass
  have hnω:(M:ℝ)/ω≤Fintype.card V:=by
    have hh:(Nω:ℝ)≤Fintype.card V:=by exact_mod_cast (show Nω≤Fintype.card V by omega)
    linarith
  have hMUReal:(M:ℝ)≤Fintype.card U:=by
    have hh: (M:ℝ)≤ω*Fintype.card V:=by simpa only [mul_comm] using (div_le_iff₀ hω).mp hnω
    exact hh.trans hU
  have hMU:M≤Fintype.card U:=by exact_mod_cast hMUReal
  exact hbase V U Γ Color (by omega) (hMU.trans hUV) hMU hUV P π hnoshort D τ A hDlo hDhi herr herrLocal weight hw p k s₀ hp hk hphys hpp hpk hps hp1 hk1 hs1 hmarked hord q hq hQ s hs hS a j ha hj hmass
end Oberwolfach
