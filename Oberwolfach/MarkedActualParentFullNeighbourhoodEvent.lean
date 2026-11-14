module

public import Oberwolfach.MarkedNeighbourhoodAdaptiveVortexEvent
public import Oberwolfach.MarkedFixedVortexEventInputs
public import Oberwolfach.MarkedFixedVortexLevelCount

@[expose] public section
/-! Full-parent row and index estimates on one globally retained outcome.
These are sampled on the fixed parent domains, not inferred from an inner
subset. An arbitrary existing event is intersected on the same law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_actual_parent_full_neighbourhood_event
    (h d:ℕ) (hd:2≤d) (β ε ρ₀ tol χ Qexp pstar ζ:ℝ)
    (hb:0≤β) (hb1:β≤1/4) (he:0<ε) (he1:ε<1/4) (hr:0<ρ₀)
    (htol:0<tol) (hχ:0<χ) (hpstar:0<pstar) (hζ:0<ζ):
    ∃ m₀:ℕ,1≤m₀ ∧ ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    ∀ (G:SimpleGraph V) (D m:ℕ),G.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D≤1→
      m₀≤m→m≤Fintype.card V→
    ∀ (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
      (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀ x l,0<l→l<2*d+1→(π^l) x≠x)→∀ L:ℕ,L<Q.length→
    let W:=markedVortexVertexType Q
    let Z:=markedVortexHubType Q
    let f:=markedVortexVertexEmbedding Q
    let g:=markedVortexHubEmbedding Q
    let ρ:=markedVortexPermutation Q π hpres;
    ∀ (p k:ℝ) (hp:0≤p) (hk:0≤k) (hphys:2*p+2*k≤1)
      (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (a:Γ) (j:Color)
      (t₀:ℝ),(∀ u,q u a=t₀)→pstar*Fintype.card V≤t₀*Fintype.card U→
    ∀ (E:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a→Prop) (err:ℝ),
    1-err≤(rawMarkedRetentionLaw π d hd a p k hp hk hphys q hq hQ s hs hS).probability E→
    1-err-2*χ-2*(Fintype.card V:ℝ)^(-Qexp)≤
      (rawMarkedRetentionLaw π d hd a p k hp hk hphys q hq hQ s hs hS).probability
        (fun z=>E z ∧ ∀ i≤L,
          MarkedRowsWithSpokes (G.comap (f i)) (ρ i) d h Finset.univ p k
            (fun u=>q (g i u)) (fun u=>s (g i u)) a j ((tol+h*ζ)*Fintype.card (W i))
            (rawMarkedRestrictPair (f i) (g i) z.1)
            (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
              (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u)) ∧
          MarkedIndicesWithSpokes (ρ i) d h Finset.univ
            (fun u=>q (g i u)) (fun u=>s (g i u)) a j ((tol+h*ζ)*Fintype.card (Z i))
            (rawMarkedRestrictPair (f i) (g i) z.1)
            (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
              (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u))):=by
  let K:=1+1/(ε/2)+1/((ε/2)*(ρ₀/8))
  have hK:1≤K:=by
    dsimp [K]
    have h1:0≤(1/(ε/2):ℝ):=by positivity
    have h2:0≤(1/((ε/2)*(ρ₀/8)):ℝ):=by positivity
    linarith
  obtain ⟨Mr,Nr,hMr,hNr,hrw⟩:=marked_retained_rows_vortex_event h d hd tol K ε χ 1 Qexp pstar ζ htol hK he (by linarith) hχ hpstar hζ
  obtain ⟨Mi,Ni,hMi,hNi,hix⟩:=marked_retained_indices_vortex_event h d hd tol K ε χ 1 Qexp pstar ζ htol hK he (by linarith) hχ hpstar hζ
  let M:=max Mr Mi
  let N:=max Nr Ni
  obtain ⟨m₁,hm₁,hsize⟩:=marked_fixed_vortex_event_size_inputs β ε ρ₀ hb hb1 he he1 hr M
  let m₀:=max m₁ N
  refine ⟨m₀,le_trans hm₁ (le_max_left _ _),?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ G D m hreg hn hD hrlo hrhi hm hmn Q π hpres hπ L hL W Z f g ρ
  have hm₁':m₁≤m:=(le_max_left _ _).trans hm
  have hnN:N≤Fintype.card V:=(le_max_right _ _).trans (hm.trans hmn)
  have hmpos:0<m:=by omega
  have hLpoly:(L+1:ℝ)≤(Fintype.card V:ℝ)^(1:ℝ):=by
    exact marked_fixed_vortex_level_count Q he (by linarith) hmpos L hL
  have hDpos:(0:ℝ)<D:=by
    have hn':(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
    linarith only [hn',hD]
  have hu2:(2:ℝ)*Fintype.card U≤D:=by
    have hh:=(div_le_iff₀ hDpos).mp hrhi
    simpa [initialIndexDensity] using hh
  have hDV:D≤Fintype.card V:=regular_degree_le_card hreg hn
  have hu:Fintype.card U≤Fintype.card V:=by
    have hv:(D:ℝ)≤Fintype.card V:=by exact_mod_cast hDV
    have hu0:(0:ℝ)≤Fintype.card U:=Nat.cast_nonneg _
    exact_mod_cast (show (Fintype.card U:ℝ)≤Fintype.card V by linarith only [hu2,hv,hu0])
  have hsizes (i:ℕ) (hi:i≤L):=hsize V U G D m hreg hn hD hrlo hrhi hm₁' Q i (by omega)
  have hminW (i:ℕ) (hi:i≤L):M≤Fintype.card (W i):=by
    have hs:=(hsizes i hi).2.1
    have hsub:(markedVortexInnerVertices Q i).card≤Fintype.card (W i):=Finset.card_le_univ _
    have hh:(M:ℝ)≤Fintype.card (W i):=by
      have hI:(0:ℝ)≤(markedVortexInnerVertices Q i).card:=Nat.cast_nonneg _
      have hsub':((markedVortexInnerVertices Q i).card:ℝ)≤Fintype.card (W i):=by exact_mod_cast hsub
      nlinarith
    exact_mod_cast hh
  have hminZ (i:ℕ) (hi:i≤L):M≤Fintype.card (Z i):=by
    have hs:=(hsizes i hi).2.2.1
    have hsub:(markedVortexInnerHubs Q i).card≤Fintype.card (Z i):=Finset.card_le_univ _
    have hh:(M:ℝ)≤Fintype.card (Z i):=by
      have hJ:(0:ℝ)≤(markedVortexInnerHubs Q i).card:=Nat.cast_nonneg _
      have hsub':((markedVortexInnerHubs Q i).card:ℝ)≤Fintype.card (Z i):=by exact_mod_cast hsub
      nlinarith
    exact_mod_cast hh
  have hstepW (i:ℕ) (hi:i<L):(Fintype.card (W (i+1)):ℝ)≤ε*Fintype.card (W i):=by
    have hh:=(Q.extended_successor_size_bounds he.le i).1
    change (Fintype.card ↥(Q.extendedVertices (i+1)):ℝ)≤ε*Fintype.card ↥(Q.extendedVertices i)
    simpa only [Fintype.card_coe] using hh
  have hstepZ (i:ℕ) (hi:i<L):(Fintype.card (Z (i+1)):ℝ)≤ε*Fintype.card (Z i):=by
    have hh:=(Q.extended_successor_size_bounds he.le i).2
    change (Fintype.card ↥(Q.extendedIndices (i+1)):ℝ)≤ε*Fintype.card ↥(Q.extendedIndices i)
    simpa only [Fintype.card_coe] using hh
  have hZW (i:ℕ) (hi:i≤L):(Fintype.card (Z i):ℝ)≤K*Fintype.card (W i):=by
    have hh:=(hsizes i hi).2.2.2.2.1
    have hsub:((markedVortexInnerVertices Q i).card:ℝ)≤Fintype.card (W i):=by exact_mod_cast (Finset.card_le_univ (markedVortexInnerVertices Q i))
    exact hh.trans (mul_le_mul_of_nonneg_left hsub (le_trans (by norm_num) hK))
  have hWZ (i:ℕ) (hi:i≤L):(Fintype.card (W i):ℝ)≤K*Fintype.card (Z i):=by
    have hh:=(hsizes i hi).2.2.2.2.2
    have hsub:((markedVortexInnerHubs Q i).card:ℝ)≤Fintype.card (Z i):=by exact_mod_cast (Finset.card_le_univ (markedVortexInnerHubs Q i))
    exact hh.trans (mul_le_mul_of_nonneg_left hsub (le_trans (by norm_num) hK))
  have hcomm:∀ i x,f i (ρ i x)=π (f i x):=fun i=>(marked_vortex_permutation_compatibility Q π hpres i).1
  intro p k hp hk hphys q hq hQ s hs hS a j t₀ ht₀ hmass E err hE
  have hrow:=hrw V U Γ Color W Z ((le_max_left _ _).trans hnN) hu G π hπ f g ρ hcomm
    (fun _=>Finset.univ) L hLpoly
    (by intro i hi;simpa using (le_max_left Mr Mi).trans (hminW i hi))
    (by intro i hi;exact (le_max_left Mr Mi).trans (hminZ i hi))
    (by intro i hi;simpa using hstepW i hi)
    (by intro i hi;simp only [Finset.card_univ];nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card (W i))])
    (by intro i hi;simpa using hZW i hi)
    (by intro i hi x;simp) p k hp hk hphys q hq hQ s hs hS a j t₀ ht₀ hmass
  have hidx:=hix V U Γ Color W Z ((le_max_right _ _).trans hnN) hu π hπ f g ρ hcomm
    (fun _=>Finset.univ) L hLpoly
    (by intro i hi;simpa using (le_max_right Mr Mi).trans (hminZ i hi))
    (by intro i hi;exact (le_max_right Mr Mi).trans (hminW i hi))
    (by intro i hi;simpa using hstepZ i hi)
    (by intro i hi;simpa using hWZ i hi)
    p k hp hk hphys q hq hQ s hs hS a j t₀ ht₀ hmass
  let μ:=rawMarkedRetentionLaw π d hd a p k hp hk hphys q hq hQ s hs hS
  let ER:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a=>∀ i≤L,
    MarkedRowsWithSpokes (G.comap (f i)) (ρ i) d h Finset.univ p k
      (fun u=>q (g i u)) (fun u=>s (g i u)) a j ((tol+h*ζ)*Fintype.card (W i))
      (rawMarkedRestrictPair (f i) (g i) z.1)
      (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u))
  let EI:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a=>∀ i≤L,
    MarkedIndicesWithSpokes (ρ i) d h Finset.univ
      (fun u=>q (g i u)) (fun u=>s (g i u)) a j ((tol+h*ζ)*Fintype.card (Z i))
      (rawMarkedRestrictPair (f i) (g i) z.1)
      (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u))
  have hr':1-χ-(Fintype.card V:ℝ)^(-Qexp)≤μ.probability ER:=by simpa only [Finset.card_univ] using hrow
  have hi':1-(χ+(Fintype.card V:ℝ)^(-Qexp))≤μ.probability EI:=by
    have hh:1-χ-(Fintype.card V:ℝ)^(-Qexp)≤μ.probability EI:=by simpa only [Finset.card_univ] using hidx
    linarith only [hh]
  have hjoin:=finiteLaw_good_intersection μ ER E err hE
  have hjoin2:=finiteLaw_good_intersection μ (fun z=>ER z ∧ E z) EI (χ+(Fintype.card V:ℝ)^(-Qexp)) hi'
  have hh:1-err-2*χ-2*(Fintype.card V:ℝ)^(-Qexp)≤μ.probability (fun z=>(ER z ∧ E z) ∧ EI z):=by
    linarith only [hr',hjoin,hjoin2]
  apply hh.trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz.1.2,?_⟩
  intro i hi
  exact ⟨hz.1.1 i hi,hz.2 i hi⟩
end Oberwolfach
