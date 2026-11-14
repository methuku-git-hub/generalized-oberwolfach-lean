module

public import Oberwolfach.OrdinaryFixedTargetMatchingInputs
public import Oberwolfach.OrdinaryCorrectedReservoirNamedWitness

@[expose] public section
/-! Fix one corrected reservoir before the edited target is selected, then
apply the matching event to the actual deletion for that same target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 65536
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fixed_reservoir_matching_targets_eventually
    (r mAbs t aAbs bAbs d:ℕ) (lamList bRate:ℝ) (hlam:0<lamList) (hbRate:0<bRate):
    ∃N:ℕ,∀{n K:ℕ},N≤n→2≤n→∀(U:Type) [Fintype U] [DecidableEq U]
    (F₀:U→SimpleGraph (Fin n)) (hF₀:∀u,(F₀ u).IsRegularOfDegree 2)
    (Cres:∀u,Finset (F₀ u).ConnectedComponent) (i₀:Fin K) (m:ℕ) (rsv θ lamMatch a γ bMatch:ℝ),
    bRate≤bMatch→
    ∀(P Host:SimpleGraph (Fin n)),Host≤P→∀(π:Equiv.Perm (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (A Z Wterm Inner:Finset (Fin n)) (Bterm B Hubs:Finset U) (ξ:ℝ)
    (γhost pstar p smin β ζ edit:ℝ) (s:U→Bool→ℝ),
    0≤γhost→0≤pstar→pstar≤p→0≤smin→smin≤rsv→(∀w,s w false=rsv)→
    0≤β→0≤ζ→bRate≤ζ→
    (∀x,(1/2+γhost)*n≤(P.degree x:ℝ))→
    (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γhost*pstar^2*n→
    β*n+(n:ℝ)^(3/4:ℝ)≤γhost*pstar^2*n*smin→lamList+2*ζ≤β→
    OrdinaryReservedCompletionTests P π d p smin s σ→
    (Inner.card:ℝ)≤min (lamList/4) (bRate/8)*n→edit≤(bRate/8)*n→
    (∀Del:SimpleGraph (Fin n),(∀x,(Del.degree x:ℝ)≤bMatch*n)→
      ∀(tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) tret),
      OrdinarySelectedMatchingFamilyResult F₀ hF₀ Cres i₀ rsv θ lamMatch a γ m d π P Del σ tret Jret)→
    let Reference:=rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))\permutationConflictGraph π (3*d)
    let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false;
    OrdinaryCorrectedProtectedReservoir r mAbs t aAbs bAbs ξ Reference (permutationConflictGraph π (3*d)) Href A Z Wterm Bterm B→
    ∃(Kabs:Finset (Sym2 (Fin n)⊕(Fin n×U))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→U→Prop),
      OrdinaryCorrectedProtectedReservoirWitness r mAbs t aAbs bAbs ξ Reference (permutationConflictGraph π (3*d)) Href A Z Wterm Bterm B Kabs JQ JH ∧
      ∀Target:SimpleGraph (Fin n),
        (∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) ((longPhysicalStateGraph P σ {0,1,2,3,4}).Adj v w))).card:ℝ)≤edit)→
        OrdinaryFixedTargetMatchingInputs F₀ hF₀ Cres i₀ rsv θ lamMatch a γ m d π P Target σ Inner Hubs Kabs lamList bRate :=by
  obtain ⟨N,hN⟩:=ordinary_fixed_reservoir_target_inputs_eventually r mAbs t aAbs bAbs d lamList bRate hlam hbRate
  refine ⟨N,?_⟩
  intro n K hn hn2 U _ _ F₀ hF₀ Cres i₀ m rsv θ lamMatch a γ bMatch hbMatch P Host hHost π σ
    A Z Wterm Inner Bterm B Hubs ξ γhost pstar p smin β ζ edit s hγ hpstar hp hsmin hs hseq hβ hζ hbζ
    hP herror hmargin hbudget hTests hInner hEdit hmatching Reference Href hRes
  obtain ⟨Kabs,JQ,JH,hWitness⟩:=ordinary_corrected_reservoir_has_witness r mAbs t aAbs bAbs ξ Reference
    (permutationConflictGraph π (3*d)) Href A Z Wterm Bterm B hRes
  refine ⟨Kabs,JQ,JH,hWitness,?_⟩
  intro Target hTarget
  have hOld:∀u:U,Disjoint (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u) (∅:Finset (Fin n)):=by simp
  have htarget:=hN n hn hn2 U P Target Host hHost π σ A Z Wterm Inner Bterm B Hubs ξ
    γhost pstar p smin rsv β ζ edit s hγ hpstar hp hsmin hs hseq hβ hζ hbζ hP herror hmargin hbudget hTests
    (fun _=>∅) hOld hInner hTarget hEdit Kabs JQ JH hWitness
  unfold OrdinaryFixedTargetMatchingInputs
  obtain ⟨hsub,_,havoid,hcol,hdel,hG,hsep,hdegree,hDelDegree,hext,_⟩:=htarget
  refine ⟨hsub,havoid,hcol,hdel,hG,hsep,hdegree,hDelDegree,hext,?_⟩
  intro tret Jret
  apply hmatching _ ?_ tret Jret
  intro x
  have hn0:(0:ℝ)≤n:=by positivity
  exact (hDelDegree x).trans (mul_le_mul_of_nonneg_right hbMatch hn0)
end Oberwolfach
