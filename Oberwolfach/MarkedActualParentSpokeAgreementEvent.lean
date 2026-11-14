module

public import Oberwolfach.MarkedActualParentFullNeighbourhoodEvent
public import Oberwolfach.RetainedMarkedRestrictionChanges

@[expose] public section
/-! Agreement of raw and retained spokes on the actual parent domains,
including rows or columns rooted outside the corresponding domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_actual_parent_spoke_agreement_event
    (d:ℕ) (hd:2≤d) (β ε ρ₀ Qexp pstar ζ:ℝ)
    (hb:0≤β) (hb1:β≤1/4) (he:0<ε) (he1:ε<1/4) (hr:0<ρ₀)
    (hpstar:0<pstar) (hζ:0<ζ):
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
    1-err-(Fintype.card V:ℝ)^(-Qexp)≤
      (rawMarkedRetentionLaw π d hd a p k hp hk hphys q hq hQ s hs hS).probability
        (fun z=>E z ∧ ∀ i≤L,
          let ω:=rawMarkedRestrictPair (f i) (g i) z.1
          let H:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u);
          (∀ b x,(∑ u,if ¬(rawMarkedPairSpokes (ρ i) d ω a j b x u↔H b x u) then (1:ℝ) else 0)≤ζ*Fintype.card (Z i)) ∧
          (∀ b u,(∑ x,if ¬(rawMarkedPairSpokes (ρ i) d ω a j b x u↔H b x u) then (1:ℝ) else 0)≤ζ*Fintype.card (W i))):=by
  let K:=1+1/(ε/2)+1/((ε/2)*(ρ₀/8))
  have hK:1≤K:=by
    dsimp [K]
    have h1:0≤(1/(ε/2):ℝ):=by positivity
    have h2:0≤(1/((ε/2)*(ρ₀/8)):ℝ):=by positivity
    linarith
  obtain ⟨M,N,hM,hN,hret⟩:=raw_marked_retention_common_event d hd 1 Qexp pstar ζ hpstar hζ
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
  have hcomm:∀ i x,f i (ρ i x)=π (f i x):=fun i=>(marked_vortex_permutation_compatibility Q π hpres i).1
  intro p k hp hk hphys q hq hQ s hs hS a j t₀ ht₀ hmass E err hE
  let S:Fin (L+1)→Finset V:=fun i=>Finset.univ.image (f i.val)
  let T:Fin (L+1)→Finset U:=fun i=>Finset.univ.image (g i.val)
  have hSc (i:Fin (L+1)):(S i).card=Fintype.card (W i.val):=by
    change (Finset.univ.image (f i.val)).card=Fintype.card (W i.val)
    rw [Finset.card_image_of_injective _ (f i.val).injective,Finset.card_univ]
  have hTc (i:Fin (L+1)):(T i).card=Fintype.card (Z i.val):=by
    change (Finset.univ.image (g i.val)).card=Fintype.card (Z i.val)
    rw [Finset.card_image_of_injective _ (g i.val).injective,Finset.card_univ]
  have hsample:=hret V U Γ Color (Fin (L+1)) hnN hu (by simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] using hLpoly)
    π hπ p k hp hk hphys q hq hQ s hs hS a t₀ ht₀ hmass S T
    (fun i=>permutation_invariant_image (f i.val) π (ρ i.val) (hcomm i.val) Finset.univ (by intro x;simp))
    (fun i=>by rw [hSc];exact hminW i.val (by omega))
    (fun i=>by rw [hTc];exact hminZ i.val (by omega)) (fun _=>True) 0 (by simp [finiteLaw_probability_true])
  simp only [sub_zero] at hsample
  let μ:=rawMarkedRetentionLaw π d hd a p k hp hk hphys q hq hQ s hs hS
  let EG:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a=>
    (∀ i:Fin (L+1),
      (∀ u,(((S i).filter (fun x=>retainedRawFamilyState π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 (x,u)≠
        rawIntervalFamilyState π d (fun e=>z.1 (Sum.inr e)) (x,u))).card:ℝ)≤ζ*(S i).card) ∧
      (∀ x,(((T i).filter (fun u=>retainedRawFamilyState π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 (x,u)≠
        rawIntervalFamilyState π d (fun e=>z.1 (Sum.inr e)) (x,u))).card:ℝ)≤ζ*(T i).card))
  have hgood:1-(Fintype.card V:ℝ)^(-Qexp)≤μ.probability EG:=by
    apply hsample.trans
    apply finiteLaw_probability_mono
    intro z hz
    exact hz.2.2
  have hint:=finiteLaw_good_intersection μ EG E err hE
  have hbound:1-err-(Fintype.card V:ℝ)^(-Qexp)≤μ.probability (fun z=>EG z ∧ E z):=by linarith only [hgood,hint]
  apply hbound.trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz.2,?_⟩
  intro i hi ω H
  have hgi:=hz.1 (⟨i,by omega⟩:Fin (L+1))
  have hc:=retainedMarked_restricted_col_changes (f i) (g i) π (ρ i) (hcomm i) d z.1 a
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j Finset.univ (ζ*Fintype.card (W i)) (by
      intro u
      have hh:=hgi.1 u
      simpa only [hSc,Finset.card_univ] using hh)
  have hrw:=retainedMarked_restricted_row_changes (f i) (g i) π (ρ i) (hcomm i) d z.1 a
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j Finset.univ (ζ*Fintype.card (Z i)) (by
      intro x
      have hh:=hgi.2 x
      simpa only [hTc,Finset.card_univ] using hh)
  exact ⟨by simpa using hrw,by simpa using hc⟩
end Oberwolfach
