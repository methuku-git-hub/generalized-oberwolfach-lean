module

public import Oberwolfach.OrdinaryVortexGeneralCertificateInnerBounds
public import Oberwolfach.OrdinaryUniformInnerHubEvent
public import Oberwolfach.OrdinaryVortexInitialLocalExactBalance

@[expose] public section
/-! For the actual corrected initial host, combine the same sampled inner
weights with exact balance and the general certificate's numerical bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_initial_selected_certificate_inputs
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U]
    (mWheel:ℕ) (P G:SimpleGraph V) (Hs:V→U→Prop) (D mv:ℕ) (β ε ρ₀:ℝ)
    (Q:Vortex U P D β ε mv) (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(Fintype.card V:ℝ)/2≤D) (hρ:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D)
    (hρhi:initialIndexDensity U D≤1) (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hm:0<mv)
    (M:ℕ) (hM:4/ε≤(M:ℝ)) (hterminal:(M:ℝ)≤ε*mv/2)
    (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (pR pH density εR εH Ledit ζedit βe βh bHub BHub ηHub capHub:ℝ)
    (δend rateParent ζh ζe γ eParent cMatch:ℝ)
    (hE:0≤Ledit) (hζcap:ζedit≤capHub) (hζrate:ζedit≤rateParent)
    (hδend:0≤δend) (hR:εR≤δend/4) (hH:εH≤δend/4)
    (hRate0:0≤rateParent) (hRate:rateParent≤δend*ε/8)
    (hζh:0<ζh) (hζe:0<ζe) (hγ:0<γ) (he:γ≤eParent) (hβeEq:βe=eParent*ε) (hc:0<cMatch)
    (hcBound:cMatch≤min (ζh*γ*(1/4:ℝ)) (ζe*(1/4:ℝ))/2):
    let F:=permutationConflictGraph π (3*d);let f:=markedVortexVertexEmbedding Q 0;let g:=markedVortexHubEmbedding Q 0;
    let I:=markedVortexInnerVertices Q 0;let B:=markedVortexInnerHubs Q 0;
    let ρi:=markedVortexPermutation Q π hπ 0;let Ploc:=P.comap f;let Floc:=F.comap f;
    let Gloc:=G.comap f;let Hloc:=fun v u=>Hs (f v) (g u);let raw:=ordinaryRawRestrictPair f g σ;
    let n:ℝ:=Fintype.card (markedVortexVertexType Q 0⊕markedVortexHubType Q 0);
    let κh:=γ*(1/4:ℝ)*ε;let κinner:=(1/4:ℝ)*ε;let θmatch:=cMatch*ε;
    OrdinaryUniformInnerHubEvent mWheel P D mv d β ε Q π hπ pR pH βe βh bHub BHub ηHub capHub
      (fun _=>density) (fun k=>εR*(markedVortexInnerVertices Q k).card)
      (fun k=>εH*(markedVortexInnerHubs Q k).card) s j σ→
    G≤P→Ledit≤ζedit*I.card→
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρi d I B pR pH density
      (εR*I.card) (εH*B.card) Ledit βe βh (fun u=>s (g u)) j raw→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    Ledit≤rateParent*n ∧ Ledit≤capHub*I.card ∧
    OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent mWheel Ploc Floc I B ρi d pR pH density
      (εR*I.card) (εH*B.card) Ledit βe βh bHub BHub ηHub (fun u=>s (g u)) j raw ∧
    Nonempty (OrdinaryMixedHubWeightsInnerScale mWheel bHub BHub ηHub Gloc Floc Hloc I B) ∧
    (∀v,Gloc.degree v=2*(Finset.univ.filter (Hloc v)).card) ∧
    (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hloc v u)).card) ∧
    I.Nonempty ∧ M≤I.card ∧ (ρ₀/8)*(I.card:ℝ)≤B.card ∧ B.card≤I.card ∧
    Fintype.card {u:markedVortexHubType Q 0 // u∉B}≤I.card^2 ∧
    Fintype.card {v:markedVortexVertexType Q 0 // v∉I}≤(ordinaryPhysicalInnerDomain I B).card^2 ∧
    εR*I.card+Ledit≤δend*I.card ∧ εH*B.card+Ledit≤δend*I.card ∧
    0<κh ∧ 0<κinner ∧ 0<θmatch ∧ κh*n≤γ*I.card ∧
    κinner*n≤(ordinaryPhysicalInnerDomain I B).card ∧ θmatch≤ζh*κh ∧ θmatch≤ζe*κinner ∧
    γ*I.card≤βe*n :=by
  intro F f g I B ρi Ploc Floc Gloc Hloc raw n κh κinner θmatch hfamily hG hLedit profile hbal hdiv
  have hcap:Ledit≤capHub*I.card:=hLedit.trans (mul_le_mul_of_nonneg_right hζcap (by positivity))
  have hIle:(I.card:ℝ)≤n:=by
    have hh:(I.card:ℝ)≤Fintype.card (markedVortexVertexType Q 0):=by exact_mod_cast Finset.card_le_univ I
    have hh':(Fintype.card (markedVortexVertexType Q 0):ℝ)≤n:=by
      dsimp [n];exact_mod_cast Fintype.card_le_of_injective Sum.inl Sum.inl_injective
    exact hh.trans hh'
  have hEdit:Ledit≤rateParent*n:=by
    have h1:=mul_le_mul_of_nonneg_right hζrate (show (0:ℝ)≤I.card by positivity)
    exact hLedit.trans (h1.trans (mul_le_mul_of_nonneg_left hIle hRate0))
  have hevent:=hfamily 0 Q.length_pos Ledit hE hcap
  have hsub:Gloc≤Ploc:=by intro v w hvw;exact hG hvw
  have hHub:=hevent Gloc Hloc (by convert profile using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _) hsub
  have hexact:=ordinary_vortex_initial_local_exact_balance P G Hs D mv β ε Q (mWheel+1) hbal hdiv
  have hnum:=ordinary_vortex_general_certificate_inner_bounds Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm 0 Q.length_pos
    M hM hterminal δend εR εH rateParent Ledit hδend hR hH hRate hEdit ζh ζe γ eParent cMatch hζh hζe hγ he hc hcBound
  rw [←hβeEq] at hnum
  refine ⟨hEdit,hcap,?_,?_,?_,?_,?_⟩
  · convert hevent using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · convert hHub using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · convert hexact.1 using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · convert hexact.2 using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · convert hnum using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
