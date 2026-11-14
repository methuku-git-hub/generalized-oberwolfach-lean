module

public import Oberwolfach.ExpandedApproximateCommonEvents
public import Oberwolfach.RawMarkedPotentialSampling
public import Oberwolfach.OrderedOrdinaryPotentialConcentration

@[expose] public section
/-! A single expanded outcome satisfies the marked and all specified
ordinary root-omitted seed concentration estimates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [Nonempty V] [LinearOrder V] [DecidableEq U]

theorem expanded_mixed_seed_common_event
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
    let μraw:=FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p₂ k₂ hp₂ hk₂ (by linarith) d hd q hq hQ s hs hS)
    let EM:=fun σ:RawMarkedOutcome V U Γ Color=>∀root,
      |typedMarkedPotentialLoad wM (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root-
        ∑W,(if root∈typedMarkedOccurrenceResources W then wM W else 0)*
          ∏a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s g j a|<t
    let EO:=fun i (σ:RawMarkedOutcome V U Γ Color)=>∀root,
      |resourcePatternLoad orderedOrdinaryResources (wO i) (fun _ _=>true) root
        (orderedOrdinaryResourceState P π d g j σ)-
        ∑W,(if root∈orderedOrdinaryResources W then wO i W else 0)*
          ∏a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s g j (orderedOrdinaryResourceEmbedding a)|<t
    let errM:ℝ:=(Fintype.card (((V×V)⊕(V×V))⊕(Bool×V×U)):ℝ)*
      (2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(((m:ℝ)+1)^4*BM/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*BM))))
    let errO:Fin K→ℝ:=fun i=>(Fintype.card ((V×V)⊕(V×U)):ℝ)*
      (2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(((ℓ i:ℝ)+1)^3*BO i/Fintype.card V)*(2*((ℓ i:ℝ)+1))*(((ℓ i:ℝ)+1)^2*BO i))))
    ∀(Prior:(Σω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,F (f ω))→Prop) (ε:ℝ),
    1-ε≤(μ.sigma (fun ω=>ν (f ω))).probability Prior →
    1-ε-(errM+∑i,errO i)≤(μ.sigma (fun ω=>ν (f ω))).probability
      (fun z=>Prior z ∧ EM (fun e=>rawExpandedApproximateCollapse e (z.1 e)) ∧
        ∀i,EO i (fun e=>rawExpandedApproximateCollapse e (z.1 e))) :=by
  intro μ f μraw EM EO errM errO Prior ε hprior
  let events:Option (Fin K)→RawMarkedOutcome V U Γ Color→Prop
    | none => EM
    | some i => EO i
  let err:Option (Fin K)→ℝ
    | none => errM
    | some i => errO i
  have hgood:∀i∈(Finset.univ:Finset (Option (Fin K))),1-err i≤μraw.probability (events i):=by
    intro i _
    cases i with
    | none =>
      exact rawMarkedPotentialLoad_common_event P π p₂ k₂ hp₂ hk₂ (by linarith) d hd q hq hQ s hs hS
        hnoshort m hm _ _ Fintype.card_pos huv wM BM hBM hwM g j t ht
    | some i =>
      have hh:=orderedOrdinary_potential_common_event P π p₂ k₂ hp₂ hk₂ (by linarith) d hd q hq hQ s hs hS
        (ℓ i) (hℓ i) Fintype.card_pos huv (wO i) (BO i) (hBO i) (hwO i) g j t ht
      simpa only [orderedOrdinary_potential_expectation P π p₂ k₂ hp₂ hk₂ (by linarith) d hd q hq hQ s hs hS hnoshort (ℓ i+1) (by have:=hℓ i;omega) (wO i) g j] using hh
  have hall:=expanded_approximate_common_events_with_prior p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν Finset.univ events err hgood Prior ε hprior
  have hequiv:∀z:(Σω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,F (f ω)),
      (Prior z ∧ ∀i∈(Finset.univ:Finset (Option (Fin K))),events i (fun e=>rawExpandedApproximateCollapse e (z.1 e))) ↔
      (Prior z ∧ EM (fun e=>rawExpandedApproximateCollapse e (z.1 e)) ∧ ∀i,EO i (fun e=>rawExpandedApproximateCollapse e (z.1 e))) :=by
    intro z
    simp only [Finset.mem_univ,true_implies]
    constructor
    · rintro ⟨hp,h⟩
      exact ⟨hp,h none,fun i=>h (some i)⟩
    · rintro ⟨hp,hm,ho⟩
      refine ⟨hp,?_⟩
      intro i
      cases i with
      | none=>exact hm
      | some i=>exact ho i
  have heq:(fun z=>(Prior z ∧ ∀i∈(Finset.univ:Finset (Option (Fin K))),events i (fun e=>rawExpandedApproximateCollapse e (z.1 e))))=
      (fun z=>(Prior z ∧ EM (fun e=>rawExpandedApproximateCollapse e (z.1 e)) ∧ ∀i,EO i (fun e=>rawExpandedApproximateCollapse e (z.1 e)))) :=by
    funext z
    exact propext (hequiv z)
  rw [heq] at hall
  simpa [err,Fintype.sum_option] using hall
end Oberwolfach
