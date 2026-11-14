module

public import Oberwolfach.MarkedActiveDifferenceJointEvent
public import Oberwolfach.MarkedFixedVortexEventInputs
public import Oberwolfach.VortexSamplingDomainSizes

@[expose] public section
/-! The active-domain event specialized to the actual pre-exposure paired
vortex. All domain choices and embeddings precede the random outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_fixed_vortex_active_neighbourhood_with_existing_event
    (h d:ℕ) (hd:2≤d) (β ε ρ₀ tol χ C Qexp pstar ζ:ℝ)
    (hb:0≤β) (hb1:β≤1/4) (he:0<ε) (he1:ε<1/4) (hr:0<ρ₀)
    (htol:0<tol) (hχ:0<χ) (hpstar:0<pstar) (hζ:0<ζ):
    ∃ m₀:ℕ,1≤m₀ ∧ ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    ∀ (G:SimpleGraph V) (D m:ℕ),G.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D ≤ 1→
      m₀≤m→m≤Fintype.card V→
    ∀ (vtx:Vortex U G D β ε m) (π:Equiv.Perm V)
      (hpres:∀ i x,π x∈vtx.extendedVertices i↔x∈vtx.extendedVertices i),
      (∀ x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∀ L:ℕ,L<vtx.length→(L+1:ℝ)≤(Fintype.card V:ℝ)^C→
    let W:=markedVortexVertexType vtx
    let Z:=markedVortexHubType vtx
    let f:=markedVortexVertexEmbedding vtx
    let g:=markedVortexHubEmbedding vtx
    let ρi:=markedVortexPermutation vtx π hpres
    let I:=markedVortexInnerVertices vtx
    let T:=markedVortexDeeperVertices vtx
    let J:=markedVortexInnerHubs vtx
    let Wrem:=markedVortexDeeperHubs vtx;
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hphys : 2*p+2*k≤1)
      (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (a : Γ) (j : Color)
      (t₀ : ℝ),(∀ u,q u a=t₀) → pstar*Fintype.card V≤t₀*Fintype.card U →
    ∀ (E:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a→Prop) (err:ℝ),
    1-err≤(rawMarkedRetentionLaw π d hd a p k hp hk hphys q hq hQ s hs hS).probability E →
    1-err-2*χ-2*(Fintype.card V:ℝ)^(-Qexp)≤
      (rawMarkedRetentionLaw π d hd a p k hp hk hphys q hq hQ s hs hS).probability
        (fun z=>E z ∧ ∀ i≤L,
          let ω := rawMarkedRestrictPair (f i) (g i) z.1
          let H := fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u);
          ∀ deltaR deltaV deltaU : ℝ,0≤deltaR→0≤deltaV→0≤deltaU→
          ∀ (DR : SimpleGraph (W i)) (DS : SimpleGraph (W i⊕Z i)),
            (∀ x,((DR.neighborFinset x∩(I i\T i)).card:ℝ)≤deltaR)→
            (∀ x,((((J i\Wrem i)).filter (fun u=>DS.Adj (Sum.inl x) (Sum.inr u))).card:ℝ)≤deltaV)→
            (∀ u,((((I i\T i)).filter (fun x=>DS.Adj (Sum.inl x) (Sum.inr u))).card:ℝ)≤deltaU)→
          MarkedRowsWithSpokes (G.comap (f i)) (ρi i) d h ((I i\T i)) p k
            (fun u=>q (g i u)) (fun u=>s (g i u)) a j
            ((tol+h*ζ)*((I i\T i)).card+h*(deltaR+deltaU))
            (rawMarkedDeleteRims ω DR.edgeFinset) (markedDeletePhysicalSpokes H DS) ∧
          MarkedIndicesWithSpokes (ρi i) d h ((J i\Wrem i))
            (fun u=>q (g i u)) (fun u=>s (g i u)) a j
            ((tol+h*ζ)*((J i\Wrem i)).card+h*deltaV)
            (rawMarkedDeleteRims ω DR.edgeFinset) (markedDeletePhysicalSpokes H DS)) := by
  let K:=1+1/(ε/2)+1/((ε/2)*(ρ₀/8))
  have hK:1≤K:=by
    dsimp [K]
    have h1:0≤(1/(ε/2):ℝ):=by positivity
    have h2:0≤(1/((ε/2)*(ρ₀/8)):ℝ):=by positivity
    linarith
  have hratio:ε<1-ε:=by linarith
  obtain ⟨M,N,hM,hN,hbase⟩:=marked_active_vortex_neighbourhood_with_existing_event h d hd tol K ε ε χ C Qexp pstar ζ
    htol hK he he.le (by linarith) hratio hχ hpstar hζ
  obtain ⟨M₀,hM₀,hsize⟩:=marked_fixed_vortex_event_size_inputs β ε ρ₀ hb hb1 he he1 hr M
  refine ⟨max M₀ N,le_trans hM₀ (le_max_left _ _),?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ G D m hreg hn hD hrlo hrhi hm hmn vtx π hpres hπ L hL hLpoly W Z f g ρi I T J Wrem
  have hm₀:M₀≤m:=(le_max_left _ _).trans hm
  have hnN:N≤Fintype.card V:=(le_max_right _ _).trans (hm.trans hmn)
  have hDpos:(0:ℝ)<D:=by
    have hn':(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
    linarith
  have hu2:(2:ℝ)*Fintype.card U≤D:=by
    have hh:=(div_le_iff₀ hDpos).mp hrhi
    simpa [initialIndexDensity] using hh
  have hdV:D≤Fintype.card V:=regular_degree_le_card hreg hn
  have hu:Fintype.card U≤Fintype.card V:=by
    have hdV':(D:ℝ)≤Fintype.card V:=by exact_mod_cast hdV
    have hU0:(0:ℝ)≤Fintype.card U:=Nat.cast_nonneg _
    exact_mod_cast (show (Fintype.card U:ℝ)≤Fintype.card V by linarith)
  have hgeometry (i:ℕ) (hi:i≤L):=marked_vortex_fixed_active_geometry vtx he.le i
  have hsizes (i:ℕ) (hi:i≤L):=hsize V U G D m hreg hn hD hrlo hrhi hm₀ vtx i (by omega)
  have hsubI:∀ i≤L,T i⊆I i:=fun i hi=>(hgeometry i hi).1
  have hsubJ:∀ i≤L,Wrem i⊆J i:=fun i hi=>(hgeometry i hi).2.1
  have hsmallI:∀ i≤L,((T i).card:ℝ)≤ε*(I i).card:=fun i hi=>(hgeometry i hi).2.2.1
  have hsmallJ:∀ i≤L,((Wrem i).card:ℝ)≤ε*(J i).card:=fun i hi=>(hgeometry i hi).2.2.2.1
  have hminI:∀ i≤L,(M:ℝ)≤(1-ε)*((I i).card:ℝ):=fun i hi=>(hsizes i hi).2.1
  have hminJ:∀ i≤L,(M:ℝ)≤(1-ε)*((J i).card:ℝ):=fun i hi=>(hsizes i hi).2.2.1
  have hstepI:∀ i<L,((I (i+1)).card:ℝ)≤ε*(I i).card:=fun i hi=>(hgeometry i (by omega)).2.2.2.2.1
  have hstepJ:∀ i<L,((J (i+1)).card:ℝ)≤ε*(J i).card:=fun i hi=>(hgeometry i (by omega)).2.2.2.2.2
  have hWI:∀ i≤L,(Fintype.card (W i):ℝ)≤K*(I i).card:=fun i hi=>(hsizes i hi).2.2.2.1
  have hZI:∀ i≤L,(Fintype.card (Z i):ℝ)≤K*(I i).card:=fun i hi=>(hsizes i hi).2.2.2.2.1
  have hWJ:∀ i≤L,(Fintype.card (W i):ℝ)≤K*(J i).card:=fun i hi=>(hsizes i hi).2.2.2.2.2
  have hcomm:∀ i x,f i (ρi i x)=π (f i x):=fun i=>(marked_vortex_permutation_compatibility vtx π hpres i).1
  have hI:∀ i≤L,∀ x,ρi i x∈I i↔x∈I i:=fun i _=>(marked_vortex_permutation_compatibility vtx π hpres i).2.1
  have hT:∀ i≤L,∀ x,ρi i x∈T i↔x∈T i:=fun i _=>(marked_vortex_permutation_compatibility vtx π hpres i).2.2
  intro p k hp hk hphys q hq hQ s hs hS a j t₀ ha hmass E err hE
  have hh:=hbase V U Γ Color W Z hnN hu G π hπ f g ρi hcomm I T J Wrem L hLpoly
    hsubI hsubJ hsmallI hsmallJ hminI hminJ hstepI hstepJ hWI hZI hWJ hI hT
    p k hp hk hphys q hq hQ s hs hS a j t₀ ha hmass E err hE
  have hsdiff (i : ℕ) :
      @SDiff.sdiff (Finset (W i))
        (@Finset.instSDiff (W i) (fun a b => Classical.propDecidable (a = b))) (I i) (T i) =
      @SDiff.sdiff (Finset (W i))
        (@Finset.instSDiff (W i) (inferInstance : DecidableEq (W i))) (I i) (T i) := by
    ext x
    simp only [Finset.mem_sdiff]
  have hinter (i : ℕ) (A B : Finset (W i)) :
      @Inter.inter (Finset (W i))
        (@Finset.instInter (W i) (fun a b => Classical.propDecidable (a = b))) A B =
      @Inter.inter (Finset (W i))
        (@Finset.instInter (W i) (inferInstance : DecidableEq (W i))) A B := by
    ext x
    simp only [Finset.mem_inter]
  simp only [hsdiff, hinter] at hh
  exact hh
end Oberwolfach
