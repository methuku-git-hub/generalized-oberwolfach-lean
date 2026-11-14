module

public import Oberwolfach.OrdinaryTriangleUniformInnerHubEvent
public import Oberwolfach.OrdinaryExpandedVortexTriangleSeparateLoadFineSupportedProductPriorCapped

@[expose] public section
/-! Attach both the all-edit inner hub event and the all-level fine cover to
one arbitrary prior on the actual expanded sample and the same coin sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_inner_fine_prior_event
    (d:ℕ) (hd:2≤d) (α ρ₀ pmin capFine:ℝ)
    (hα:0<α) (hρ₀:0<ρ₀) (hpmin:0<pmin) (hpmin1:pmin≤1) (hcapFine:0<capFine):
    ∃c C κfine:ℝ,0<c ∧ 0<C ∧ 0<κfine ∧ κfine≤1 ∧ κfine≤capFine ∧
    ∀(aLoad ε ξ b Bweight ηHub Kdom χinner χfine eParent hParent:ℝ),
      0<aLoad→aLoad≤κfine→0<ε→ε<1/4→ε≤κfine→ε≤ρ₀/16→
      0<ξ→0<χinner→0<χfine→2/ε≤Kdom→
      1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom→b≤c→
      (4*C/pmin^(3*2+1))*Kdom^2≤Bweight→0<eParent→0<hParent→
    ∃t eEvent hEvent cap:ℝ,0<t ∧ 0<eEvent ∧ 0<hEvent ∧ 0<cap ∧
      eEvent≤eParent ∧ hEvent≤hParent ∧
    ∀β:ℝ,0≤β→β≤1/4→β≤α/8→β≤κfine→ξ+2*β<ηHub→∃v₀:ℕ,1≤v₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∀(θhost p k p₂ k₂ u:ℝ) (hθ:1/2≤θhost) (hthreshold:cycleThreshold 3≤θhost)
      (hdegree:(θhost+α)*Fintype.card V≤D)
      (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1),
    ∀(pH:ℝ),pmin≤2*p→pmin≤pH→pH≤1→2*p=initialIndexDensity U D*pH→
    ∃weight:∀i,OrdinaryCycle ((P.comap (markedVortexVertexEmbedding Q i)).induce
        ((markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i))) 3→ℝ,
    (∀i,i<Q.length→OrdinaryInnerHubWeightSetupGeneral 2 (P.comap (markedVortexVertexEmbedding Q i))
      ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
      (markedVortexInnerVertices Q i) (weight i) pmin (2*p) pH
      (2*pH*(markedVortexInnerHubs Q i).card/(2*p)) β ξ (2*((3*d:ℕ):ℝ)) c C b Bweight ηHub Kdom) ∧
    ∀(density tR tH:ℕ→ℝ) (q:U→Γ→ℝ) (hq:∀w z,0≤q w z) (hQ:∀w,∑z,q w z≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑z,q w z)) (j:Color) (hj:∀w,s w j=pH),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (νcoins:FiniteLaw (Sym2 V→Bool))
      (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V→Bool)→Prop) (a:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let Inner:=OrdinaryTriangleUniformInnerHubEvent P D vsize d β ε Q π hπ (2*p) pH
      (eParent*ε) (hParent*ε) c (4*C/pmin^(3*2+1)) ηHub cap density tR tH s j
    let Fine:=OrdinaryFixedVortexTriangleSeparateLoadFineCoverEvent d κfine aLoad P D vsize β ε Q π hπ j;
    1-a≤((μ.sigma ν).prod νcoins).probability E→
    1-(a+χinner+χfine)≤((μ.sigma ν).prod νcoins).probability
      (fun z=>(E z ∧ Inner (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
        Fine (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) :=by
  obtain ⟨c,C,hc,hC,hinner⟩:=ordinary_expanded_uniform_edit_event_with_setups 2 d (by omega) hd α hα
  obtain ⟨κfine,hκfine,hκfine1,hκfinecap,hfine⟩:=
    ordinary_expanded_vortex_triangle_separate_load_fine_supported_product_prior_capped α ρ₀ pmin capFine
      hα hρ₀ hpmin hpmin1 hcapFine
  refine ⟨c,C,κfine,hc,hC,hκfine,hκfine1,hκfinecap,?_⟩
  intro aLoad ε ξ b Bweight ηHub Kdom χinner χfine eParent hParent ha haκ hε hε1 hεκ hερ
    hξ hχinner hχfine hK hKdom hb hB he hh
  obtain ⟨t,eEvent,hEvent,cap,ht,heEvent,hhEvent,hcap,heBound,hhBound,hinner⟩:=
    hinner ε ρ₀ pmin ξ b Bweight ηHub Kdom χinner eParent hParent hε hε1 hρ₀ hpmin hpmin1 hξ hχinner
      hK hKdom hb hB he hh
  refine ⟨t,eEvent,hEvent,cap,ht,heEvent,hhEvent,hcap,heBound,hhBound,?_⟩
  intro β hβ hβ1 hβα hβκ hgap
  obtain ⟨vInner,hvInner,hinner⟩:=hinner β hβ hβ1 hβα hgap
  obtain ⟨vFine,hvFine,hfine⟩:=hfine aLoad ha haκ ε χfine hε hε1 hεκ hερ hχfine β hβ hβ1 hβα hβκ d hd
  refine ⟨max vInner vFine,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hρlo hρhi hv Q π hπ hnoshort θhost p k p₂ k₂ u
    hθ hthreshold hdegree hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq
  have hpR1:2*p≤1:=by linarith
  obtain ⟨weight,hweight,hinner⟩:=hinner V U Γ Color P D vsize hreg hn hρlo hρhi (by omega) Q π hπ hnoshort
    θhost p k p₂ k₂ u hθ hthreshold hdegree hp hk hp₂ hk₂ hu hsum pH hpR hpR1 hpH hpH1 hpEq
  refine ⟨weight,hweight,?_⟩
  intro density tR tH q hq hQ s hs hS j hj R _ ν νcoins E a μ Inner Fine hE
  have hJ:=hinner density tR tH q hq hQ s hs hS j ν νcoins E a hE
  have hJ':1-(a+χinner)≤((μ.sigma ν).prod νcoins).probability
      (fun z=>E z ∧ Inner (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) :=by
    dsimp [Inner,OrdinaryTriangleUniformInnerHubEvent]
    linarith only [hJ]
  have hF:=hfine V U Γ Color P D vsize hreg hn hρlo hρhi (by omega) Q π hπ hnoshort
    θhost hθ hthreshold hdegree p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq
    q hq hQ s hs hS j hj ν νcoins
    (fun z=>E z ∧ Inner (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) (a+χinner) hJ'
  exact hF.1
end Oberwolfach
