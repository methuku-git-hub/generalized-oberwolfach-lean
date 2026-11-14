module

public import Oberwolfach.MarkedRestrictedBalanceVortex
public import Oberwolfach.MarkedBalanceSpokeChanges
public import Oberwolfach.RetainedMarkedRestrictionChanges
public import Oberwolfach.RawMarkedRetentionEvent
public import Oberwolfach.PermutationInvariantImage

@[expose] public section

/-! The four restricted balance estimates after global retention, with
all outer roots. The error uses the caller's original scale M i, even
when the row and hub restrictions are smaller. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_retained_balance_vortex_event
    (m d : ℕ) (hd : 2≤d) (ε K η χ C Q pstar ζ : ℝ)
    (hε : 0<ε) (hK : 1≤K) (hη : 0<η) (hη1 : η<1) (hχ : 0<χ)
    (hpstar : 0<pstar) (hζ : 0<ζ) :
    ∃ M₀ N : ℕ,1≤M₀ ∧ 1≤N ∧ ∀ (V U Γ Color : Type) (W Z : ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [Nonempty V] [DecidableEq U]
      [∀ i,Fintype (W i)] [∀ i,Fintype (Z i)] [∀ i,LinearOrder (W i)] [∀ i,DecidableEq (Z i)],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V),
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (f : ∀ i,W i↪oV) (g : ∀ i,Z i↪U) (ρ : ∀ i,Equiv.Perm (W i)),
      (∀ i x,f i (ρ i x)=π (f i x)) →
    ∀ (A : ∀ i,Finset (W i)) (B : ∀ i,Finset (Z i)) (M : ℕ→ℕ) (L : ℕ),
      (L+1:ℝ)≤(Fintype.card V:ℝ)^C →
      (∀ i≤L,M₀≤(A i).card) → (∀ i≤L,M₀≤(B i).card) →
      (∀ i<L,(M (i+1):ℝ)≤η*M i) →
      (∀ i≤L,(A i).card≤M i) → (∀ i≤L,(B i).card≤M i) →
      (∀ i≤L,∀ x,ρ i x∈A i ↔ x∈A i) →
      (∀ i≤L,(Fintype.card (W i):ℝ)≤K*M i) → (∀ i≤L,(Fintype.card (Z i):ℝ)≤K*M i) →
    ∀ (D : ℕ→ℝ) (δP : ℝ),0≤δP → δP≤ε/4 →
      (∀ i≤L,∀ x : W i,|(((P.comap (f i)).neighborFinset x∩A i).card:ℝ)-D i|≤δP*M i) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hphys : 2*p+2*k≤1)
      (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (a : Γ) (j : Color)
      (s₀ t₀ : ℝ),(∀ u,q u a=t₀) → (∀ u,s u j=s₀) →
      (∀ i≤L,p*D i=s₀*(B i).card) → (∀ i≤L,k*D i=t₀*(B i).card) → s₀=(m:ℝ)*t₀ →
      pstar*Fintype.card V≤t₀*Fintype.card U →
    1-χ-(Fintype.card V:ℝ)^(-Q)≤
      (rawMarkedRetentionLaw π d hd a p k hp hk hphys q hq hQ s hs hS).probability
        (fun z=>∀ i≤L,MarkedRestrictedBalanceWithSpokes (P.comap (f i)) (ρ i) d m (A i) (B i)
          ((ε+(m+2:ℕ)*ζ)*M i) (rawMarkedRestrictPair (f i) (g i) z.1)
          (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u))) := by
  obtain ⟨mret,N,hm,hN1,hret⟩ := raw_marked_retention_common_event d hd C Q pstar ζ hpstar hζ
  obtain ⟨Mb,hMb1,hbalance⟩ := marked_restricted_balance_vortex_event m d hd ε K η χ hε hK hη hη1 hχ
  refine ⟨max mret Mb,N,hm.trans (le_max_left _ _),hN1,?_⟩
  intro V U Γ Color W Z _ _ _ _ _ _ _ _ _ _ _ hn hu P π hπ f g ρ hcomm A B M L hL hA hB hstep hAM hBM hInv hW hZ D δP hδP hδε hP p k hp hk hphys q hq hQ s hs hS a j s₀ t₀ ha hj hD0 hDK hratio hmass
  let S : Fin (L+1)→Finset V := fun i=>(A i.val).image (f i.val)
  let T : Fin (L+1)→Finset U := fun i=>(B i.val).image (g i.val)
  have hSc (i : Fin (L+1)) : (S i).card=(A i.val).card := Finset.card_image_of_injective _ (f i.val).injective
  have hTc (i : Fin (L+1)) : (T i).card=(B i.val).card := Finset.card_image_of_injective _ (g i.val).injective
  let E := fun σ : RawMarkedOutcome V U Γ Color=>∀ i≤L,
    RawMarkedRestrictedBalance (P.comap (f i)) (ρ i) d m a j (A i) (B i) (ε*M i)
      (rawMarkedRestrictPair (f i) (g i) σ)
  have hE : 1-χ≤(FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS)).probability E :=
    hbalance V U Γ Color W Z P π hπ f g ρ hcomm A B M L
      (fun i hi=>((le_max_right mret Mb).trans (hA i hi)).trans (hAM i hi)) hstep
      (fun i hi=>Finset.card_pos.mp (lt_of_lt_of_le (by omega) (hA i hi)))
      (fun i hi=>Finset.card_pos.mp (lt_of_lt_of_le (by omega) (hB i hi)))
      hAM hBM hInv hW hZ D δP hδP hδε hP p k hp hk hphys q hq hQ s hs hS a j s₀ t₀ ha hj hD0 hDK hratio
  have hb := hret V U Γ Color (Fin (L+1)) hn hu
    (by simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] using hL)
    π hπ p k hp hk hphys q hq hQ s hs hS a t₀ ha hmass S T
    (fun i=>permutation_invariant_image (f i.val) π (ρ i.val) (hcomm i.val) (A i.val) (hInv i.val (by omega)))
    (fun i=>by rw [hSc];exact (le_max_left mret Mb).trans (hA i.val (by omega)))
    (fun i=>by rw [hTc];exact (le_max_left mret Mb).trans (hB i.val (by omega))) E χ hE
  apply hb.trans
  apply finiteLaw_probability_mono
  intro z hz i hi
  have hc := retainedMarked_restricted_col_changes (f i) (g i) π (ρ i) (hcomm i) d z.1 a
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j (A i) (ζ*M i) (by
      intro u
      have hh := (hz.2.2 (⟨i,by omega⟩ : Fin (L+1))).1 u
      rw [hSc] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hAM i hi)) hζ.le))
  have hr := retainedMarked_restricted_row_changes (f i) (g i) π (ρ i) (hcomm i) d z.1 a
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j (B i) (ζ*M i) (by
      intro x
      have hh := (hz.2.2 (⟨i,by omega⟩ : Fin (L+1))).2 x
      rw [hTc] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hBM i hi)) hζ.le))
  have hh := markedRestrictedBalance_spoke_changes (P.comap (f i)) (ρ i) d m (A i) (B i) a j
    (ε*M i) (ζ*M i) (by positivity) (rawMarkedRestrictPair (f i) (g i) z.1) _ (hz.1 i hi) hr hc
  have he : ε*M i+(m+2:ℕ)*(ζ*M i)=(ε+(m+2:ℕ)*ζ)*M i := by ring
  rw [he] at hh
  exact hh

end Oberwolfach
