module

public import Oberwolfach.OrdinarySameSampleRowsAndCuts
public import Oberwolfach.OrdinaryGeneralInnerDeepPriorEventBeforeSpacing

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

theorem ordinary_general_inner_deep_rows_cuts_before_spacing
    (m:ℕ) (hm:3≤m) (α ρ₀ pmin αcut:ℝ)
    (hα:0<α) (hρ₀:0<ρ₀) (hpmin:0<pmin) (hpmin1:pmin≤1)
    (hαcut:0<αcut) (hαcut1:αcut≤1/2) (hαcutα:αcut≤α/2):
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∃K:ℕ,0<K ∧ ∃a ε₀ ρ θdeep:ℝ,0<a ∧ 0<ε₀ ∧ 0<ρ ∧ 0<θdeep ∧
    ∀(aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut:ℝ),
      0<aLoad→aLoad≤a→0<ε→ε<1/4→ε≤a→ε≤ρ₀/16→
      0<ξ→0<χinner→0<χdeep→2/ε≤Kdom→
      1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom→b≤c→
      (4*C/pmin^(3*m+1))*Kdom^m≤Bweight→0<eParent→0<hParent→
      0<εR→0<εH→0<χone→0<χtwo→0<χcut→
    ∃t eEvent hEvent cap:ℝ,0<t ∧ 0<eEvent ∧ 0<hEvent ∧ 0<cap ∧
      eEvent≤eParent ∧ hEvent≤hParent ∧
    ∀(d:ℕ) (hd:2≤d),∀β:ℝ,0≤β→β≤1/4→β≤α/8→β≤ε₀→ξ+2*β<ηHub→∃v₀:ℕ,1≤v₀ ∧
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
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
      (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V→Bool)→Prop) (loss:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let νcoins:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin)
    let Inner:=OrdinaryUniformInnerHubEvent m P D vsize d β ε Q π hπ (2*p) pH
      (eParent*ε) (hParent*ε) c (4*C/pmin^(3*m+1)) ηHub cap density tR tH s j
    let Deep:=OrdinaryFixedVortexDeepCoverEvent m K d a aLoad ρ θdeep P D vsize β ε Q π hπ j;
    1-loss≤((μ.sigma ν).prod νcoins).probability E→
    1-(loss+χinner+χdeep+χone+χtwo+χcut)≤((μ.sigma ν).prod νcoins).probability
      (fun z=>((((E z ∧ Inner (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
        Deep (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
        OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D vsize β ε Q π hπ (2*p) pH s j
          (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
        OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D vsize β ε Q π hπ (2*p) pH s j
          (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
        ∀i,i<Q.length→OrdinaryInducedRimCutEvent (Q.extendedVertices (i+1))
          (sampledOrientation (rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) z.2) αcut pmin) :=by
  obtain ⟨c,C,hc,hC,K,hK,a,ε₀,ρ,θdeep,ha,hε₀,hρ,hθ,hmain⟩:=
    ordinary_general_inner_deep_prior_event_before_spacing m hm α ρ₀ pmin hα hρ₀ hpmin hpmin1
  refine ⟨c,C,hc,hC,K,hK,a,ε₀,ρ,θdeep,ha,hε₀,hρ,hθ,?_⟩
  intro aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut
    haLoad haLoadA hε hε1 hεa hερ hξ hχinner hχdeep hK hKdom hb hB he hh hεR hεH hχone hχtwo hχcut
  obtain ⟨t,eEvent,hEvent,cap,ht,heEvent,hhEvent,hcap,heBound,hhBound,hmain⟩:=
    hmain aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent haLoad haLoadA hε hε1 hεa hερ
      hξ hχinner hχdeep hK hKdom hb hB he hh
  refine ⟨t,eEvent,hEvent,cap,ht,heEvent,hhEvent,hcap,heBound,hhBound,?_⟩
  intro d hd β hβ hβ1 hβα hβε hgap
  obtain ⟨vInner,hvInner,hmain⟩:=hmain d hd β hβ hβ1 hβα hβε hgap
  obtain ⟨vRows,hvRows,hrows⟩:=ordinary_same_sample_rows_and_cuts 3 d hd α αcut pmin β ε ρ₀ εR εH χone χtwo χcut
    hα hαcut hαcut1 hαcutα hpmin hβ hβα hβ1 hε hε1 hρ₀ hεR hεH hχone hχtwo hχcut
  refine ⟨max vInner vRows,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hρlo hρhi hv Q π hπ hnoshort θhost p k p₂ k₂ u
    hθ hthreshold hdegree hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq
  obtain ⟨weight,hweight,hmain⟩:=hmain V U Γ Color P D vsize hreg hn hρlo hρhi (by omega) Q π hπ hnoshort
    θhost p k p₂ k₂ u hθ hthreshold hdegree hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq
  refine ⟨weight,hweight,?_⟩
  intro density tR tH q hq hQ s hs hS j hj R _ ν E loss μ νcoins Inner Deep hE
  have hprior:=hmain density tR tH q hq hQ s hs hS j hj ν νcoins E loss hE
  have hdegree':(1/2+α)*Fintype.card V≤D:=by
    have hn0:(0:ℝ)≤Fintype.card V:=by positivity
    nlinarith [mul_nonneg (show 0≤θhost-1/2 by linarith) hn0]
  let Prior:=fun z:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V→Bool)=>
    (E z ∧ Inner (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
      Deep (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))
  have hprior':1-(loss+χinner+χdeep)≤((μ.sigma ν).prod νcoins).probability Prior:=by exact hprior
  exact hrows V U Γ Color P (permutationConflictGraph π (3*d)) D vsize hreg hn hdegree' hρlo hρhi (by omega) Q π hπ hnoshort le_rfl
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hpR q hq hQ s hs hS j pH hj ν Prior (loss+χinner+χdeep) hprior'
end Oberwolfach
