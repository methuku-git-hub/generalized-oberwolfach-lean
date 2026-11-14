module

public import Oberwolfach.OrdinaryGeneralInnerDeepBeforeFailure
public import Oberwolfach.OrdinaryNamedInnerHubBeforeFailure
public import Oberwolfach.OrdinaryExpandedGeneralDeepProductPrior

@[expose] public section
/-! Attach the all-edit inner hub event and the separate-load deep cover for
an arbitrary ordinary wheel length to one prior and one reference-coin law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 65000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_inner_deep_before_load
    (m:ℕ) (hm:3≤m) (α ρ₀ pmin:ℝ)
    (hα:0<α) (hρ₀:0<ρ₀) (hpmin:0<pmin) (hpmin1:pmin≤1):
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∃K:ℕ,0<K ∧ ∃a ε₀ ρ θdeep:ℝ,0<a ∧ 0<ε₀ ∧ 0<ρ ∧ 0<θdeep ∧
    ∀(ε ξ b Bweight ηHub Kdom eParent hParent:ℝ),
      0<ε→ε<1/4→ε≤a→ε≤ρ₀/16→
      0<ξ→2/ε≤Kdom→
      1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom→b≤c→
      (4*C/pmin^(3*m+1))*Kdom^m≤Bweight→0<eParent→0<hParent→
    ∃t eEvent hEvent cap:ℝ,0<t ∧ 0<eEvent ∧ 0<hEvent ∧ 0<cap ∧
      eEvent≤eParent ∧ hEvent≤hParent ∧
    ∀aLoad:ℝ,0<aLoad→aLoad≤a→
    ∀χinner χdeep:ℝ,0<χinner→0<χdeep→∀(d:ℕ) (hd:2≤d),∀β:ℝ,0≤β→β≤1/4→β≤α/8→β≤ε₀→ξ+2*β<ηHub→∃v₀:ℕ,1≤v₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∀(θhost p k p₂ k₂ u:ℝ) (hθ:1/2≤θhost) (hthreshold:cycleThreshold (m+1)≤θhost)
      (hdegree:(θhost+α)*Fintype.card V≤D)
      (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1),
    ∀(pH:ℝ),pmin≤2*p→pmin≤pH→pH≤1→2*p=initialIndexDensity U D*pH→
    ∃weight:∀i,OrdinaryCycle ((P.comap (markedVortexVertexEmbedding Q i)).induce
        ((markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i))) (m+1)→ℝ,
    (∀i,i<Q.length→OrdinaryInnerHubWeightSetupGeneral m (P.comap (markedVortexVertexEmbedding Q i))
      ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
      (markedVortexInnerVertices Q i) (weight i) pmin (2*p) pH
      (2*pH*(markedVortexInnerHubs Q i).card/(2*p)) β ξ (2*((3*d:ℕ):ℝ)) c C b Bweight ηHub Kdom) ∧
    ∀(density tR tH:ℕ→ℝ) (q:U→Γ→ℝ) (hq:∀w z,0≤q w z) (hQ:∀w,∑z,q w z≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑z,q w z)) (j:Color) (hj:∀w,s w j=pH),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (νcoins:FiniteLaw (Sym2 V→Bool))
      (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V→Bool)→Prop) (loss:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let Inner:=OrdinaryUniformInnerHubEvent m P D vsize d β ε Q π hπ (2*p) pH
      (eParent*ε) (hParent*ε) c (4*C/pmin^(3*m+1)) ηHub cap density tR tH s j
    let Deep:=OrdinaryFixedVortexDeepCoverEvent m K d a aLoad ρ θdeep P D vsize β ε Q π hπ j;
    1-loss≤((μ.sigma ν).prod νcoins).probability E→
    1-(loss+χinner+χdeep)≤((μ.sigma ν).prod νcoins).probability
      (fun z=>(E z ∧ Inner (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
        Deep (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) :=by
  obtain ⟨c,C,hc,hC,hinner⟩:=ordinary_named_inner_hub_before_failure m (by omega) α hα
  obtain ⟨K,hK,a,ε₀,ρ,θdeep,ha,hε₀,hρ,hθ,hdeep⟩:=
    ordinary_expanded_general_deep_product_prior m hm α ρ₀ pmin hα hρ₀ hpmin hpmin1
  refine ⟨c,C,hc,hC,K,hK,a,ε₀,ρ,θdeep,ha,hε₀,hρ,hθ,?_⟩
  intro ε ξ b Bweight ηHub Kdom eParent hParent hε hε1 hεa hερ
    hξ hK hKdom hb hB he hh
  obtain ⟨t,eEvent,hEvent,cap,ht,heEvent,hhEvent,hcap,heBound,hhBound,hinner⟩:=
    hinner ε ρ₀ pmin ξ b Bweight ηHub Kdom eParent hParent hε hε1 hρ₀ hpmin hpmin1 hξ
      hK hKdom hb hB he hh
  refine ⟨t,eEvent,hEvent,cap,ht,heEvent,hhEvent,hcap,heBound,hhBound,?_⟩
  intro aLoad haLoad haLoadA χinner χdeep hχinner hχdeep d hd β hβ hβ1 hβα hβε hgap
  obtain ⟨vInner,hvInner,hinner⟩:=hinner χinner hχinner d hd β hβ hβ1 hβα hgap
  obtain ⟨vDeep,hvDeep,hdeep⟩:=hdeep ε χdeep hε hε1 hεa hερ hχdeep β hβ hβ1 hβα hβε aLoad haLoad haLoadA d hd
  refine ⟨max vInner vDeep,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hρlo hρhi hv Q π hπ hnoshort θhost p k p₂ k₂ u
    hθ hthreshold hdegree hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq
  have hpR1:2*p≤1:=by linarith
  obtain ⟨weight,hweight,hinner⟩:=hinner V U Γ Color P D vsize hreg hn hρlo hρhi (by omega) Q π hπ hnoshort
    θhost p k p₂ k₂ u hθ hthreshold hdegree hp hk hp₂ hk₂ hu hsum pH hpR hpR1 hpH hpH1 hpEq
  refine ⟨weight,hweight,?_⟩
  intro density tR tH q hq hQ s hs hS j hj R _ ν νcoins E loss μ Inner Deep hE
  have hJ:=hinner density tR tH q hq hQ s hs hS j ν νcoins E loss hE
  change 1-loss-χinner≤((μ.sigma ν).prod νcoins).probability
    (fun z=>E z ∧ Inner (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) at hJ
  have hJ':1-(loss+χinner)≤((μ.sigma ν).prod νcoins).probability
      (fun z=>E z ∧ Inner (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) :=by
    linarith only [hJ]
  have hD:=hdeep V U Γ Color P D vsize hreg hn hρlo hρhi (by omega) Q π hπ hnoshort
    θhost p k p₂ k₂ u hθ hthreshold hdegree hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq
    q hq hQ s hs hS j hj ν νcoins
    (fun z=>E z ∧ Inner (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) (loss+χinner) hJ'
  exact hD
end Oberwolfach
