module

public import Oberwolfach.MarkedPackingLoadSpokeChanges
public import Oberwolfach.RetainedMarkedRestrictionChanges
public import Oberwolfach.RawMarkedRetentionEvent
public import Oberwolfach.PermutationInvariantImage

@[expose] public section

/-! Inner rim/spoke and external spoke-root potential loads on all fixed vortex levels of
the actual globally retained experiment. Each level keeps its supplied
parent weighting and normalization throughout both exposures. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_retained_packing_load_vortex_event
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
        (fun z=>∀ i≤L,MarkedPackingLoadsWithSpokes (P.comap (f i)) (ρ i) d m (D i) p k s₀ (weight i) a j
          (b i) (fun z=>q (g i z)) (fun z=>s (g i z)) (τ+ε+11*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*K*ζ)
          (rawMarkedRestrictPair (f i) (g i) z.1)
          (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u))) := by
  obtain ⟨mret,N,hmret,hN1,hret⟩ := raw_marked_retention_common_event d hd C Q pret ζ hpret hζ
  obtain ⟨Ml,hMl1,hloads⟩ := marked_packing_loads_vortex_event m d hm hd B pstar ε K η χ
    hB hpstar hε hη hη1 hχ
  refine ⟨max mret Ml,N,hmret.trans (le_max_left _ _),hN1,?_⟩
  intro V U Γ Color W Z H _ _ _ _ _ _ _ _ _ _ _ _ _ hn hu P π hπ f g b ρ hcomm L hL hW hZ hstep hZW hHW D τ A hDlo hDhi weight hw p k s₀ hp hk hphys hpp hpk hps hp1 hk1 hs1 hmarked hord q hq hQ s hs hS a j ha hj hmass
  let S : Fin (L+1)→Finset V := fun i=>Finset.univ.image (f i.val)
  let T : Fin (L+1)→Finset U := fun i=>Finset.univ.image (g i.val)
  have hSc (i : Fin (L+1)) : (S i).card=Fintype.card (W i.val) := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ (f i.val).injective,Finset.card_univ]
  have hTc (i : Fin (L+1)) : (T i).card=Fintype.card (Z i.val) := by
    dsimp [T]
    rw [Finset.card_image_of_injective _ (g i.val).injective,Finset.card_univ]
  let E := fun σ : RawMarkedOutcome V U Γ Color=>∀ i≤L,
    RawMarkedPackingLoads (P.comap (f i)) (ρ i) d m (D i) p k s₀ (weight i) a j
      (b i) (fun z=>q (g i z)) (fun z=>s (g i z)) (τ+ε)
      (rawMarkedRestrictPair (f i) (g i) σ)
  have hE : 1-χ≤(FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk.le hphys d hd q hq hQ s hs hS)).probability E :=
    hloads V U Γ Color W Z H P π hπ f g b ρ hcomm L
      (fun i hi=>(le_max_right mret Ml).trans (hW i hi)) hstep hZW hHW D τ A hDlo hDhi weight hw
      p k s₀ hp hk hphys hpp hpk hps hp1 hk1 hs1 hmarked hord q hq hQ s hs hS a j ha hj
  have hb := hret V U Γ Color (Fin (L+1)) hn hu
    (by simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] using hL)
    π hπ p k hp.le hk.le hphys q hq hQ s hs hS a (s₀/m) ha hmass S T
    (fun i=>permutation_invariant_image (f i.val) π (ρ i.val) (hcomm i.val) Finset.univ (by simp))
    (fun i=>by rw [hSc];exact (le_max_left mret Ml).trans (hW i.val (by omega)))
    (fun i=>by rw [hTc];exact (le_max_left mret Ml).trans (hZ i.val (by omega))) E χ hE
  apply hb.trans
  apply finiteLaw_probability_mono
  intro z hz i hi
  have hKi : 0≤K := le_trans (by norm_num) hK
  have hc := retainedMarked_restricted_col_changes (f i) (g i) π (ρ i) (hcomm i) d z.1 a
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j Finset.univ (K*ζ*Fintype.card (W i)) (by
      intro u
      have hh := (hz.2.2 (⟨i,by omega⟩ : Fin (L+1))).1 u
      rw [hSc] at hh
      exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_right hK (show 0≤ζ*Fintype.card (W i) by positivity)]))
  have hr := retainedMarked_restricted_row_changes (f i) (g i) π (ρ i) (hcomm i) d z.1 a
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j Finset.univ (K*ζ*Fintype.card (W i)) (by
      intro x
      have hh := (hz.2.2 (⟨i,by omega⟩ : Fin (L+1))).2 x
      rw [hTc] at hh
      exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_left (hZW i hi) hζ.le]))
  have hni : 0<Fintype.card (W i) := lt_of_lt_of_le (by omega) (hW i hi)
  have hh := markedPackingLoads_spoke_changes (P.comap (f i)) (ρ i) d m hm hni (D i) τ A B
    (hDlo i hi) (hDhi i hi) p k s₀ pstar hpstar hpp hpk hps hp1 hk1 hs1 hB.le
    (weight i) (hw i hi) a j (b i) (hHW i hi) (fun z=>q (g i z)) (fun z=>s (g i z)) (τ+ε) (K*ζ*Fintype.card (W i)) (by positivity)
    (rawMarkedRestrictPair (f i) (g i) z.1) _ (hz.1 i hi) hr hc
  have hn0 : (Fintype.card (W i):ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hni)
  have he : τ+ε+11*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*(K*ζ*Fintype.card (W i))/Fintype.card (W i)=
      τ+ε+11*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*K*ζ := by field_simp [hn0] <;> ring
  rw [he] at hh
  exact hh

end Oberwolfach
