module

public import Oberwolfach.ExpandedMixedSeedCommonEvent

@[expose] public section
/-! Root-omitted concentration events, indexed by the fixed seed families. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [Nonempty V] [LinearOrder V] [DecidableEq U]

def rawMarkedSeedConcentrated (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (t:ℝ)
    (w:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (σ:RawMarkedOutcome V U Γ Color):Prop:=
  ∀root,|typedMarkedPotentialLoad w (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root-
    ∑W,(if root∈typedMarkedOccurrenceResources W then w W else 0)*
      ∏a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p k q s g j a|<t

def rawOrdinarySeedConcentrated (P:SimpleGraph V) (π:Equiv.Perm V) (d r:ℕ)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (t:ℝ)
    (w:OrderedOrdinaryWheel (U:=U) π (3*d) r→ℝ) (σ:RawMarkedOutcome V U Γ Color):Prop:=
  ∀root,|resourcePatternLoad orderedOrdinaryResources w (fun _ _=>true) root
      (orderedOrdinaryResourceState P π d g j σ)-
    ∑W,(if root∈orderedOrdinaryResources W then w W else 0)*
      ∏a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal P π d p k q s g j (orderedOrdinaryResourceEmbedding a)|<t

def mixedSeedFailureBound (V U:Type) [Fintype V] [Fintype U] (d m K:ℕ) (ℓ:Fin K→ℕ) (BM:ℝ) (BO:Fin K→ℝ) (t:ℝ):ℝ:=
  (Fintype.card (((V×V)⊕(V×V))⊕(Bool×V×U)):ℝ)*
    (2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(((m:ℝ)+1)^4*BM/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*BM))))+
  ∑i,(Fintype.card ((V×V)⊕(V×U)):ℝ)*
    (2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(((ℓ i:ℝ)+1)^3*BO i/Fintype.card V)*(2*((ℓ i:ℝ)+1))*(((ℓ i:ℝ)+1)^2*BO i))))

theorem expanded_mixed_named_seed_event
    (P:SimpleGraph V) (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d m K:ℕ) (hd:2≤d) (hm:3≤m)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x) (huv:Fintype.card U≤Fintype.card V)
    (ℓ:Fin K→ℕ) (hℓ:∀i,2≤ℓ i)
    (wM:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (wO:∀i,OrderedOrdinaryWheel (U:=U) π (3*d) (ℓ i+1)→ℝ)
    (BM:ℝ) (BO:Fin K→ℝ) (hBM:0<BM) (hBO:∀i,0<BO i)
    (hwM:∀W,0≤wM W ∧ wM W≤BM/(Fintype.card V:ℝ)^m)
    (hwO:∀i W,0≤wO i W ∧ wO i W≤BO i/(Fintype.card V:ℝ)^(ℓ i))
    (g:Γ) (j:Color) (t:ℝ) (ht:0<t)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀a,Fintype (F a)] (ν:∀a,FiniteLaw (F a)):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    ∀(Prior:(Σω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,F (f ω))→Prop) (ε:ℝ),
    1-ε≤(μ.sigma (fun ω=>ν (f ω))).probability Prior →
    1-ε-mixedSeedFailureBound V U d m K ℓ BM BO t≤
      (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>Prior z ∧
        rawMarkedSeedConcentrated P π d m p₂ k₂ q s g j t wM (fun e=>rawExpandedApproximateCollapse e (z.1 e)) ∧
        ∀i,rawOrdinarySeedConcentrated P π d (ℓ i+1) p₂ k₂ q s g j t (wO i) (fun e=>rawExpandedApproximateCollapse e (z.1 e))) :=by
  intro μ f Prior ε hprior
  have h:=expanded_mixed_seed_common_event P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d m K hd hm q hq hQ s hs hS
    hnoshort huv ℓ hℓ wM wO BM BO hBM hBO hwM hwO g j t ht F ν Prior ε hprior
  simpa only [mixedSeedFailureBound,rawMarkedSeedConcentrated,rawOrdinarySeedConcentrated] using h
end Oberwolfach
