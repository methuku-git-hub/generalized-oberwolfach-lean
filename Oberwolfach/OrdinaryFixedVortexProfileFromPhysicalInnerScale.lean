module

public import Oberwolfach.OrdinaryFixedVortexCleanupBalance
public import Oberwolfach.OrdinaryCleanupProfileFromDeepSample
public import Oberwolfach.OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent
public import Oberwolfach.OrdinaryPhysicalEditToTypedChanges

@[expose] public section
/-! A bounded actual physical edit of the common sample yields the cleanup
profile, near balance and adaptive hub weights on a fixed vortex level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_fixed_vortex_profile_from_physical_edit_inner_scale
    (mWheel:ℕ) (P F:SimpleGraph V) (D vsize:ℕ) (β ε θ α pR pH εR εH L βe βh η b Bweight ηHub:ℝ)
    (Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (hn:0<Fintype.card V) (hreg:P.IsRegularOfDegree D) (hρ:0< initialIndexDensity U D)
    (hβ:0≤β) (hpR:0≤pR) (hpR1:pR≤1) (hpH:0≤pH) (hεR:0≤εR) (hεH:0≤εH) (hL:0≤L)
    (hθ:1/2≤θ) (hβα:β≤2*α) (hdegree:(θ+α)*Fintype.card V≤D)
    (hpEq:pR=initialIndexDensity U D*pH) (hs:∀u,s u j=pH)
    (hgood:OrdinaryFixedVortexRowIndexEvent 3 d εR εH P F D vsize β ε Q π hπ pR pH s j σ)
    (i:ℕ) (hi:i<Q.length):
    let I:=markedVortexInnerVertices Q i;let B:=markedVortexInnerHubs Q i;
    let f:=markedVortexVertexEmbedding Q i;let g:=markedVortexHubEmbedding Q i;
    let ρ:=markedVortexPermutation Q π hπ i;let raw:=ordinaryRawRestrictPair f g σ;
    ∀(G:SimpleGraph (markedVortexVertexType Q i)) (H:markedVortexVertexType Q i→markedVortexHubType Q i→Prop),
    G≤P.comap f→Disjoint G (F.comap f)→
    (∀w:markedVortexVertexType Q i⊕markedVortexHubType Q i,
      ((changed ((ordinaryPhysicalGraph (rawWheelGraph (P.comap f) raw) (rawWheelSpokes ρ d raw j)).neighborFinset w)
        ((ordinaryPhysicalGraph G H).neighborFinset w)).card:ℝ)≤L)→
    βe*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)+εR*I.card+3*L≤
      pR^2*pH*(2*(θ+α-β/2)-1)*I.card→
    βh*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)+εH*B.card+2*L≤pH^2*B.card→
    (initialIndexDensity U D*pH)*β*I.card+εR*I.card+2*(εH*B.card)+3*L≤η*I.card→
    OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent mWheel (P.comap f) (F.comap f) I B ρ d pR pH (θ+α-β/2)
      (εR*I.card) (εH*B.card) L βe βh b Bweight ηHub (fun u=>s (g u)) j raw→
    OrdinaryCleanupParentProfiles (P.comap f) G (F.comap f) H ρ d I B pR pH (θ+α-β/2)
      (εR*I.card) (εH*B.card) L βe βh (fun u=>s (g u)) j raw ∧
    (∀v:I,|((G.induce (I:Set _)).degree v:ℝ)-2*(Finset.univ.filter (fun u:B=>H v.val u.val)).card|≤η*I.card) ∧
    Nonempty (OrdinaryMixedHubWeightsInnerScale mWheel b Bweight ηHub G (F.comap f) H I B):=by
  intro I B f g ρ raw G H hGP hdis hphys hext hhub hmargin hevent
  have hin:=ordinary_fixed_vortex_cleanup_inputs P F D vsize β ε θ α pR pH εR εH Q π hπ d s j σ
    hn hreg hρ hβ hpH hdegree hgood i hi
  have hchange:=ordinary_physical_edit_to_typed_changes (rawWheelGraph (P.comap f) raw) G (rawWheelSpokes ρ d raw j) H L hphys
  have hdensity:1/2≤θ+α-β/2:=by linarith
  have hprofile:=ordinary_cleanup_profile_from_deep_sample (P.comap f) G (F.comap f) H ρ d I B
    pR pH (θ+α-β/2) (εR*I.card) (εH*B.card) L βe βh (fun u=>s (g u)) j raw
    hpR hpR1 hpH hdensity (fun u=>hs (g u)) hdis
    (by intro v;convert hin.1 v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by convert hin.2.2.1 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by convert hin.2.2.2 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by convert hchange.1 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by convert hchange.2.2 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by convert hchange.2.1 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hext hhub
  have hnear:=ordinary_fixed_vortex_cleanup_balance P F D vsize β ε θ α pR pH εR εH L βe βh η Q π hπ d s j σ
    hn hreg hρ hβ hpH hεR hεH hL hdegree hpEq hgood i hi G H
    (by convert hprofile using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hmargin
  refine ⟨?_,?_,?_⟩
  · convert hprofile using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hnear using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · have hw:=hevent G H (by convert hprofile using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hGP
    convert hw using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
