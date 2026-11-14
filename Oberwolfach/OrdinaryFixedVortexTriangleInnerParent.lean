module

public import Oberwolfach.OrdinaryVortexTriangleInnerNumericInputs
public import Oberwolfach.EndpointConditionsFromCleanupProfile
public import Oberwolfach.OrdinaryFixedVortexConflictDegree
public import Oberwolfach.OrdinaryVortexLevelParentDensityBalance
public import Oberwolfach.OrdinaryEndpointDegreeFromInnerDensity

@[expose] public section
/-! The original regular-host vortex, one cleanup profile, and the
preselected inner-scale numeric hierarchy yield the endpoint geometry and
all row, index, conflict and endpoint error bounds on the same raw outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
variable {P:SimpleGraph V} {D mv:ℕ} {β ε ρ₀:ℝ} (Q:Vortex U P D β ε mv)

theorem ordinary_fixed_vortex_triangle_inner_parent
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:(Fintype.card V:ℝ)/2≤D)
    (hρ:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hm:0<mv) (i:ℕ) (hi:i<Q.length)
    (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (α pmin εfactor ηend εrows δ εcount t lam:ℝ)
    (hα:0<α) (hβα:β≤α/8) (hpmin:0<pmin)
    (num:OrdinaryTriangleInnerNumericParameters pmin (ρ₀/8) εfactor ηend εrows δ εcount t lam)
    (hβbalance:β≤2*δ*(ρ₀/8)*pmin)
    (M:ℕ) (hM:32≤M) (hMε:4/ε≤(M:ℝ))
    (hMb:((2*(3*d):ℕ):ℝ)≤lam*M) (hterminal:(M:ℝ)≤ε*mv/2)
    (θhost pR pH εR εH Ledit tP rateParent βe βh:ℝ)
    (hθ:cycleThreshold 3≤θhost) (hdegree:(θhost+α)*Fintype.card V≤D)
    (hpR:pmin≤pR) (hpR1:pR≤1) (hpH:pmin≤pH) (hpH1:pH≤1)
    (hpEq:pR=initialIndexDensity U D*pH) (hεR:2*εR≤εcount) (hεH:2*εH≤εcount)
    (hE:0≤Ledit) (hrate:rateParent≤lam*ε/4)
    (hEdit:Ledit≤rateParent*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i))
    (htP:tP≤t) (j:Color) (s:markedVortexHubType Q i→Color→ℝ)
    (raw:RawWheelOutcome (markedVortexVertexType Q i) (markedVortexHubType Q i) Γ Color)
    (R:SimpleGraph (markedVortexVertexType Q i)) (S:markedVortexVertexType Q i→markedVortexHubType Q i→Prop):
    let f:=markedVortexVertexEmbedding Q i;let I:=markedVortexInnerVertices Q i;let B:=markedVortexInnerHubs Q i;
    let ρi:=markedVortexPermutation Q π hπ i;let Ploc:=P.comap f;
    let Floc:=(permutationConflictGraph π (3*d)).comap f;
    let density:=θhost+α-β/2;let L:ℝ:=2*((3*d:ℕ):ℝ);
    OrdinaryCleanupParentProfiles Ploc R Floc S ρi d I B pR pH density
      (εR*I.card) (εH*B.card) Ledit βe βh s j raw→
    R≤Ploc\Floc→
    EndpointPhysicalEditedConditions Ploc R Floc S I B Iᶜ ρi d j (ρ₀/8) pmin pR pH L Ledit δ raw ∧
    I.Nonempty ∧ M≤I.card ∧
    Fintype.card {v:markedVortexVertexType Q i // v∉I}≤I.card^2 ∧
    Fintype.card {u:markedVortexHubType Q i // u∉B}≤I.card^2 ∧
    (∀v,Floc.degree v≤2*(3*d)) ∧ (∀v,(Floc.degree v:ℝ)≤L) ∧
    (εR*I.card)+4*Ledit≤εcount*I.card ∧ (εH*B.card)+3*Ledit≤εcount*B.card ∧
    (εR*I.card)+4*Ledit≤εrows*I.card ∧ (εH*B.card)+3*Ledit≤εrows*B.card ∧
    L≤(I.card:ℝ)/24 ∧ L≤εfactor*I.card ∧
    δ+(2*40+(1+2*40)/(2*(ρ₀/8)*pmin))*L/I.card+
      (tP+10*(40/((ρ₀/8)*pmin^5))*Ledit/I.card)≤ηend ∧
    (3/4:ℝ)≤density ∧
    (∀x∉I,∀v∈insert x I,(3/4:ℝ)*I.card≤((I∩Ploc.neighborFinset v).card:ℝ)):=by
  intro f I B ρi Ploc Floc density L profile hQ
  have hL:0≤L:=by dsimp [L];positivity
  have hLeq:L=((2*(3*d):ℕ):ℝ):=by dsimp [L];simp
  have hLb:L≤((2*(3*d):ℕ):ℝ):=hLeq.le
  have hR:(εR*I.card)≤εcount*I.card/2:=by
    have hh:=mul_le_mul_of_nonneg_right hεR (show (0:ℝ)≤I.card by positivity)
    nlinarith only [hh]
  have hH:(εH*B.card)≤εcount*B.card/2:=by
    have hh:=mul_le_mul_of_nonneg_right hεH (show (0:ℝ)≤B.card by positivity)
    nlinarith only [hh]
  have hs:=ordinary_vortex_triangle_inner_numeric_inputs Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm i hi
    pmin εfactor ηend εrows δ εcount t lam num hpmin M (2*(3*d)) hM hMε hMb hterminal
    L Ledit (εR*I.card) (εH*B.card) tP δ rateParent hL hLb hE hrate hEdit hR hH htP le_rfl
  obtain ⟨hI,hIs,hBI,hB,hIv,hBu,hrowCount,hindexCount,hrow,hindex,hLA,hLfactor,herr⟩:=hs
  have hFnat:∀v,Floc.degree v≤2*(3*d):=by
    intro v
    exact ordinary_fixed_vortex_conflict_degree P D mv β ε Q π hπ i (3*d) v
  have hF:∀v,(Floc.degree v:ℝ)≤L:=by
    intro v
    have hh:((Floc.degree v:ℝ))≤((2*(3*d):ℕ):ℝ):=by exact_mod_cast hFnat v
    simpa only [hLeq] using hh
  have hρpos:0 < initialIndexDensity U D:=hρ.trans_le hρlo
  have hpH0:0≤pH:=hpmin.le.trans hpH
  have hfields:=ordinary_vortex_level_parent_density_balance P D mv β ε θhost α (initialIndexDensity U D) pH
    Q hn hreg rfl hρpos hβ hpH0 hdegree i (by omega)
  have hparent:∀v,|pR*(I∩Ploc.neighborFinset v).card-2*pH*B.card|≤pR*β*I.card:=by
    intro v
    have hh:=hfields.2 v
    rw [←hpEq] at hh
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hδpos:=num.delta_pos
  have hpHpos:0<pH:=hpmin.trans_le hpH
  have hbal:pR*β*I.card≤δ*(2*B.card*pH):=by
    have hcoef:pR*β≤2*δ*(ρ₀/8)*pH:=by
      have h1:pR*β≤β:=by nlinarith only [hpR1,hβ]
      have h2:2*δ*(ρ₀/8)*pmin≤2*δ*(ρ₀/8)*pH:=by gcongr
      linarith only [h1,hβbalance,h2]
    have hIr:0≤(I.card:ℝ):=by positivity
    have h1:=mul_le_mul_of_nonneg_right hcoef hIr
    have h2:=mul_le_mul_of_nonneg_left hBI (show 0≤2*δ*pH by positivity)
    nlinarith only [h1,h2]
  have hgeom:=endpoint_conditions_from_cleanup_profile Ploc R Floc S I B ρi d j s (ρ₀/8) pmin pR pH density
    (εR*I.card) (εH*B.card) L Ledit βe βh δ (pR*β*I.card) raw profile (Finset.card_pos.mpr hI) hQ
    (by positivity) hpmin hL hE num.delta_pos.le hBI hB hpR hpR1 hpH hpH1 hF hparent hbal
  have hthreshold:cycleThreshold 3≤density:=by dsimp [density];linarith
  have hdensity:(3/4:ℝ)≤density:=cycleThreshold_triangle_lower.trans hthreshold
  have hdeg:=ordinary_endpoint_degree_from_inner_density Ploc I density hthreshold hfields.1
  exact ⟨hgeom,hI,hIs,hIv,hBu,hFnat,hF,hrowCount,hindexCount,hrow,hindex,hLA,hLfactor,herr,hdensity,hdeg⟩
end Oberwolfach
