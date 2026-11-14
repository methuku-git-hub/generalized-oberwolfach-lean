module

public import Oberwolfach.MarkedRetainedPackingLoadVortex
public import Oberwolfach.MarkedPackingLoadsAfterPhysicalDeletion

@[expose] public section

/-! On one event for the original retained sampling experiment, the fixed
packing weights control every later physical deletion on every supplied
domain. All potential roots and the original normalizations are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_packing_adaptive_vortex_event
    (m d : ℕ) (hm : 3≤m) (hd : 2≤d) (B pstar ε K η χ C Q pret ζ : ℝ)
    (hB : 0<B) (hpstar : 0<pstar) (hε : 0<ε) (hK : 1≤K)
    (hη : 0<η) (hη1 : η<1) (hχ : 0<χ) (hpret : 0<pret) (hζ : 0<ζ) :
    ∃ M₀ N : ℕ,1≤M₀ ∧ 1≤N ∧ ∀ (V U Γ Color : Type) (W Z H : ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [Nonempty V] [DecidableEq U]
      [∀ i,Fintype (W i)] [∀ i,Fintype (Z i)] [∀ i,Fintype (H i)]
      [∀ i,LinearOrder (W i)] [∀ i,DecidableEq (Z i)] [∀ i,DecidableEq (H i)],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V),
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (f : ∀ i,W i↪oV) (g : ∀ i,Z i↪U) (b : ∀ i,H i↪Z i) (ρ : ∀ i,Equiv.Perm (W i)),
      (∀ i x,f i (ρ i x)=π (f i x)) →
    ∀ L : ℕ,(L+1:ℝ)≤(Fintype.card V:ℝ)^C →
      (∀ i≤L,M₀≤Fintype.card (W i)) → (∀ i≤L,M₀≤Fintype.card (Z i)) →
      (∀ i<L,(Fintype.card (W (i+1)):ℝ)≤η*Fintype.card (W i)) →
      (∀ i≤L,(Fintype.card (Z i):ℝ)≤K*Fintype.card (W i)) →
      (∀ i≤L,Fintype.card (H i)≤Fintype.card (W i)) →
    ∀ (D : ℕ→ℝ) (τ A : ℝ),
      (∀ i≤L,(Fintype.card (W i):ℝ)/2≤D i) → (∀ i≤L,D i≤2*Fintype.card (W i)) →
    ∀ weight : ∀ i,(Fin (m+1)→W i)→ℝ,
      (∀ i≤L,SuccessorSequenceWeightConditions (P.comap (f i)) (ρ i) (3*d) (D i) τ A B (weight i)) →
    ∀ (p k s₀ : ℝ) (hp : 0<p) (hk : 0<k) (hphys : 2*p+2*k≤1),
      pstar≤p → pstar≤k → pstar≤s₀ → p≤1 → k≤1 → s₀≤1 →
      (∀ i≤L,(Fintype.card (H i):ℝ)*(s₀/m)=D i*k) →
      (∀ i≤L,(Fintype.card (H i):ℝ)*(s₀/m)*m=D i*p) →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (a : Γ) (j : Color),
      (∀ u,q u a=s₀/m) → (∀ u,s u j=s₀) → pret*Fintype.card V≤(s₀/m)*Fintype.card U →
    1-χ-(Fintype.card V:ℝ)^(-Q)≤
      (rawMarkedRetentionLaw π d hd a p k hp.le hk.le hphys q hq hQ s hs hS).probability
        (fun z=>∀ i≤L,∀ δ : ℝ,0≤δ→
          ∀ (DR : SimpleGraph (W i)) (DS : SimpleGraph (W i⊕Z i)),
          (∀ x,(DR.degree x:ℝ)≤δ)→(∀ x,(DS.degree x:ℝ)≤δ)→
          MarkedPackingLoadsWithSpokes (P.comap (f i)) (ρ i) d m (D i) p k s₀ (weight i) a j
            (b i) (fun z=>q (g i z)) (fun z=>s (g i z))
            (τ+ε+11*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*K*ζ+
              33*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*δ/Fintype.card (W i))
            (rawMarkedDeleteRims (rawMarkedRestrictPair (f i) (g i) z.1) DR.edgeFinset)
            (markedDeletePhysicalSpokes
              (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
                (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a))
                  z.2 a j b (f i x) (g i u)) DS)) := by
  obtain ⟨M,N,hM,hN,hbase⟩ := marked_retained_packing_load_vortex_event m d hm hd B pstar ε K η χ C Q pret ζ
    hB hpstar hε hK hη hη1 hχ hpret hζ
  refine ⟨M,N,hM,hN,?_⟩
  intro V U Γ Color W Z H _ _ _ _ _ _ _ _ _ _ _ _ _ hn hu P π hπ f g b ρ hcomm L hL hW hZ hstep hZW hHW D τ A hDlo hDhi weight hw p k s₀ hp hk hphys hpp hpk hps hp1 hk1 hs1 hmarked hord q hq hQ s hs hS a j ha hj hmass
  have he := hbase V U Γ Color W Z H hn hu P π hπ f g b ρ hcomm L hL hW hZ hstep hZW hHW D τ A hDlo hDhi weight hw p k s₀ hp hk hphys hpp hpk hps hp1 hk1 hs1 hmarked hord q hq hQ s hs hS a j ha hj hmass
  apply he.trans
  apply finiteLaw_probability_mono
  intro z hz i hi δ hδ DR DS hDR hDS
  exact marked_packing_loads_after_physical_deletion (P.comap (f i)) (ρ i) d m hm
    (lt_of_lt_of_le (by omega) (hW i hi)) (D i) τ A B (hDlo i hi) (hDhi i hi)
    p k s₀ pstar hpstar hpp hpk hps hp1 hk1 hs1 hB.le (weight i) (hw i hi)
    a j (b i) (hHW i hi) (fun z=>q (g i z)) (fun z=>s (g i z)) _ δ hδ _ _ (hz i hi) DR DS hDR hDS

end Oberwolfach
