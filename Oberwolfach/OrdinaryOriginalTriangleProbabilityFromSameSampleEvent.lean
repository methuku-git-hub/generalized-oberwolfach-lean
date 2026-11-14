module

public import Oberwolfach.OrdinaryOriginalTriangleNamedUniformSplitProbability

@[expose] public section
/-! Transfer the matching/correction prior and its same-sample wheel tests
together to the original retention law, without an additional failure loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_triangle_probability_from_same_sample_event
    (m k d K:ℕ) (hd:2≤d) (βfreq ρ₀ α θhost ε βv:ℝ)
    (δ θ aRow γrow σbal lamMatch lamPlace ξedit bMatch rate ξroot:ℝ)
    (mAbs tAbs aAbs bAbs:ℕ)
    (hterminal:OrdinaryOriginalTerminalConditionalPreparationAt 3 m k d K hd βfreq ρ₀ α θhost ε βv
      δ θ aRow γrow σbal lamMatch lamPlace ξedit bMatch rate ξroot mAbs tAbs aAbs bAbs) :
    ∃N:ℕ,∀n qCount D:ℕ,N≤ n→ qCount≤ n→
    ∀(F:Fin qCount→ SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (Allowed:Set ℕ),(∀u,AllowedCycleLengths (F u) Allowed)→
    ∀(P:SimpleGraph (Fin n)),P.IsRegularOfDegree D→(θhost+α)*(n:ℝ)≤ D→
      ρ₀≤ initialIndexDensity (Fin qCount) D→ initialIndexDensity (Fin qCount) D≤ 1→
    ∀(mv:ℕ) (Q:Vortex (Fin qCount) P D βv ε mv) (π:Equiv.Perm (Fin n)),
      (∀x l,0<l→ l<2*d+1→(π^l) x≠x)→
    ∀(i₀:Fin K) (rsv:ℝ) (Cres:∀u,Finset (F u).ConnectedComponent)
      (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ (βfreq/200) d)
      (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ ℝ)
      (seed:(Fin (m+1)→ Fin n)→ ℝ) (τ tMatch ξMatch ζSel lamSel ζDel ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent:ℝ)
      (BO:Fin K→ ℝ),
      OrdinaryOriginalSelectorFactorWitness n qCount D 3 m k d K hd ρ₀ θ lamMatch aRow γrow lamPlace ζDel
        (βfreq/200) τ tMatch ξMatch bMatch σbal ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent α BO F hF P π i₀ rsv Cres sampling w seed→
    ∀(q₀:ℕ) (χlocal χglobal χhub χcol ξabs:ℝ)
      (R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type)
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (κcoin:FiniteLaw (Sym2 (Fin n)→Bool))
      (Tests:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool)→Prop)
      (bprob:ℝ),
    let p:=initialIndexDensity (Fin qCount) D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ ((m:ℝ)+1) D
    let marks:=ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1)
    let spokes:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((m:ℝ)+1)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd marks sampling.hq sampling.hQ spokes sampling.hs sampling.hS);
    let E:=OrdinaryAssignedCorrectionEvent 3 d mAbs aAbs bAbs tAbs q₀ n qCount K D hd (θ/2) χlocal χglobal χhub χcol ξabs
      P (permutationConflictGraph π (3*d)) π F hF i₀ rsv θ ρ₀ (βfreq/200) m sampling
      (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length)
      (Q.extendedIndices Q.length) (Q.extendedIndices 1) (Q.extendedIndices 1) R ν
      ζevent χpair χlist χbal χbd χnbr χpairR χpath Cres lamMatch aRow γrow σbal aEvent ζDel lamPlace bMatch w seed tMatch ξMatch;
    bprob≤((μ.sigma ν).prod κcoin).probability (fun z=>E z∧Tests z)→
    2*mv≤mAbs→
    (∀z,E z→Tests z→
      OrdinaryTriangleUniformMatchedWheelOutcome (mAbs:=mAbs) (tAbs:=tAbs) (aAbs:=aAbs) (bAbs:=bAbs)
        d P D mv βv ε rate ξroot Q π F Cres (Finset.univ\Q.extendedVertices 1)
        (Q.extendedVertices Q.length) (Q.extendedIndices Q.length) ξabs
        (ordinaryTriangleAssignedReservoirCost d δ aRow γrow ξedit σbal sampling.u) z.1.1)→
    let aBound:=2^(tAbs*tAbs)*aAbs;let bBound:=2^(tAbs*tAbs)*bAbs;
    bprob≤(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin (initialIndexDensity (Fin qCount) D)
      (by unfold initialIndexDensity;positivity)
      (by rw [←sampling.hphysical];exact sampling.hsum))).probability
      (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) (Q.extendedVertices 1) ξedit (aBound*aBound+aBound*bBound) F)
 :=by
  obtain ⟨N,hN⟩:=ordinary_original_triangle_named_uniform_split_probability m k d K hd βfreq ρ₀ α θhost ε βv
    δ θ aRow γrow σbal lamMatch lamPlace ξedit bMatch rate ξroot mAbs tAbs aAbs bAbs hterminal
  refine ⟨N,?_⟩
  intro n qCount D hn hq F hF Allowed hAllowed P hreg hdegree hρlo hρhi mv Q π hnoshort
    i₀ rsv Cres sampling w seed τ tMatch ξMatch ζSel lamSel ζDel ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent BO hwitness
    q₀ χlocal χglobal χhub χcol ξabs R _ ν κcoin Tests bprob p p₂ marks spokes μ E hprob hAbs hWheel aBound bBound
  apply hN n qCount D hn hq F hF Allowed hAllowed P hreg hdegree hρlo hρhi mv Q π hnoshort
    i₀ rsv Cres sampling w seed τ tMatch ξMatch ζSel lamSel ζDel ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent BO hwitness
    q₀ χlocal χglobal χhub χcol ξabs R ν κcoin (fun z=>E z∧Tests z) bprob hprob hAbs
  intro z hz
  exact ⟨hz.1,hWheel z hz.1 hz.2⟩
end Oberwolfach
