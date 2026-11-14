module

public import Oberwolfach.MarkedRowsVortex
public import Oberwolfach.MarkedNeighbourhoodSpokeChanges
public import Oberwolfach.RetainedMarkedRestrictionChanges
public import Oberwolfach.RawMarkedRetentionEvent
public import Oberwolfach.PermutationInvariantImage

@[expose] public section

/-! All bounded row estimates at all fixed vortex levels, on the actual
single globally retained marked experiment. The retained spoke relation
is restricted from that outcome; no local retention law is substituted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_retained_rows_vortex_event
    (h d : ℕ) (hd : 2≤d) (ε K η χ C Q pstar ζ : ℝ)
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
    ∀ (A : ∀ i,Finset (W i)) (L : ℕ),
      (L+1:ℝ)≤(Fintype.card V:ℝ)^C →
      (∀ i≤L,M₀≤(A i).card) → (∀ i≤L,M₀≤Fintype.card (Z i)) →
      (∀ i<L,((A (i+1)).card:ℝ)≤η*(A i).card) →
      (∀ i≤L,(Fintype.card (W i):ℝ)≤K*(A i).card) →
      (∀ i≤L,(Fintype.card (Z i):ℝ)≤K*(A i).card) →
      (∀ i≤L,∀ x,ρ i x∈A i ↔ x∈A i) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hphys : 2*p+2*k≤1)
      (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (a : Γ) (j : Color)
      (t₀ : ℝ),(∀ u,q u a=t₀) → pstar*Fintype.card V≤t₀*Fintype.card U →
    1-χ-(Fintype.card V:ℝ)^(-Q)≤
      (rawMarkedRetentionLaw π d hd a p k hp hk hphys q hq hQ s hs hS).probability
        (fun z=>∀ i≤L,MarkedRowsWithSpokes (P.comap (f i)) (ρ i) d h (A i) p k
          (fun u=>q (g i u)) (fun u=>s (g i u)) a j ((ε+h*ζ)*(A i).card)
          (rawMarkedRestrictPair (f i) (g i) z.1)
          (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u))) := by
  obtain ⟨m,N,hm,hN1,hret⟩ := raw_marked_retention_common_event d hd C Q pstar ζ hpstar hζ
  obtain ⟨M,hM1,hrows⟩ := marked_rows_vortex_event h d hd ε K η χ hε hK hη hη1 hχ
  refine ⟨max m M,N,hm.trans (le_max_left _ _),hN1,?_⟩
  intro V U Γ Color W Z _ _ _ _ _ _ _ _ _ _ _ hn hu P π hπ f g ρ hcomm A L hL hA hZ hstep hW hZU hInv p k hp hk hphys q hq hQ s hs hS a j t₀ ha hmass
  let S : Fin (L+1)→Finset V := fun i=>(A i.val).image (f i.val)
  let T : Fin (L+1)→Finset U := fun i=>Finset.univ.image (g i.val)
  have hSc (i : Fin (L+1)) : (S i).card=(A i.val).card := Finset.card_image_of_injective _ (f i.val).injective
  have hTc (i : Fin (L+1)) : (T i).card=Fintype.card (Z i.val) := by
    dsimp [T]
    rw [Finset.card_image_of_injective _ (g i.val).injective,Finset.card_univ]
  let E := fun σ : RawMarkedOutcome V U Γ Color=>∀ i≤L,
    RawMarkedRows (P.comap (f i)) (ρ i) d h (A i) p k
      (fun u=>q (g i u)) (fun u=>s (g i u)) a j (ε*(A i).card) (rawMarkedRestrictPair (f i) (g i) σ)
  have hE : 1-χ≤(FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS)).probability E :=
    hrows V U Γ Color W Z P π hπ f g ρ hcomm A L
      (fun i hi=>(le_max_right m M).trans (hA i hi)) hstep hW hZU p k hp hk hphys q hq hQ s hs hS a j
  have hb := hret V U Γ Color (Fin (L+1)) hn hu
    (by simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] using hL)
    π hπ p k hp hk hphys q hq hQ s hs hS a t₀ ha hmass S T
    (fun i=>permutation_invariant_image (f i.val) π (ρ i.val) (hcomm i.val) (A i.val) (hInv i.val (by omega)))
    (fun i=>by rw [hSc];exact (le_max_left m M).trans (hA i.val (by omega)))
    (fun i=>by rw [hTc];exact (le_max_left m M).trans (hZ i.val (by omega))) E χ hE
  apply hb.trans
  apply finiteLaw_probability_mono
  intro z hz i hi
  let H : Bool→W i→Z i→Prop := fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u)
  have hc := retainedMarked_restricted_col_changes (f i) (g i) π (ρ i) (hcomm i) d z.1 a
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j (A i) (ζ*(A i).card) (by
      intro u
      have hh := (hz.2.2 (⟨i,by omega⟩ : Fin (L+1))).1 u
      rw [hSc] at hh
      exact hh)
  have hh := markedRows_spoke_changes (P.comap (f i)) (ρ i) d h (A i) p k
    (fun u=>q (g i u)) (fun u=>s (g i u)) a j (ε*(A i).card) (ζ*(A i).card)
    (by positivity) (rawMarkedRestrictPair (f i) (g i) z.1) H (hz.1 i hi) hc
  have he : ε*(A i).card+h*(ζ*(A i).card)=(ε+h*ζ)*(A i).card := by ring
  rw [he] at hh
  exact hh

end Oberwolfach
