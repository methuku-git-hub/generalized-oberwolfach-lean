module

public import Oberwolfach.MarkedRetainedBalanceVortex
public import Oberwolfach.MarkedRestrictedSampleBalance
public import Oberwolfach.MarkedActualIterationBalanceError
public import Oberwolfach.RetainedMarkedSpokeGeometry

@[expose] public section

/-! The single retained experiment supplies the finite balance inputs at
all fixed vortex domains, and their deterministic bounds after every later
permitted deletion. The earlier sampling law and the original scales M i
are unchanged; no event is chosen after the deleted sets are known. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_finite_balance_adaptive_vortex_event
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
        (fun z=>∀ i≤L,
          let σi := rawMarkedRestrictPair (f i) (g i) z.1
          let Hi := fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u)
          let E := MarkedSampleArc (P.comap (f i)) (ρ i) (3*d) (fun e=>σi (Sum.inl e)) false
          let KArc := MarkedSampleArc (P.comap (f i)) (ρ i) (3*d) (fun e=>σi (Sum.inl e)) true
          let S := Finset.univ.filter (fun s:W i×Z i=>Hi false s.1 s.2∨Hi true s.1 s.2)
          let err := (ε+(m+2:ℕ)*ζ)*M i;
          (∀ v j,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
            (fun e:KArc=>e.val.1) (fun e=>e.val.2) (Hi true) Finset.univ S m (A i) (B i) v j|≤err) ∧
          ∀ (KA : Finset (E⊕KArc)) (KS : Finset (W i×Z i)),KS⊆S→
          let R := markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
            (fun e:KArc=>e.val.1) (fun e=>e.val.2) (ρ i) KA KS;
          R.filter (markedInnerResource (A i) (B i))=∅→
          ∀ δ:ℝ,0≤δ→
          (∀ physical v,(((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2)
            (fun e:KArc=>e.val.1) (fun e=>e.val.2) (ρ i) (Hi false) (Hi true) physical v).filter
            (fun e=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
              (fun e:KArc=>e.val.1) (fun e=>e.val.2) (ρ i) (Hi false) (Hi true) e∈
                R.filter (markedStarResource (A i) (B i)))).card:ℝ)≤δ)→
          let σ' := rawMarkedDeleteRims σi (markedSampleArcSetGraph (P.comap (f i)) (ρ i) d σi KA).edgeFinset
          let H' := markedDeletePhysicalSpokes Hi (markedFiniteSpokeGraph KS)
          let E' := MarkedSampleArc (P.comap (f i)) (ρ i) (3*d) (fun e=>σ' (Sum.inl e)) false
          let K' := MarkedSampleArc (P.comap (f i)) (ρ i) (3*d) (fun e=>σ' (Sum.inl e)) true
          let S' := Finset.univ.filter (fun s:W i×Z i=>H' false s.1 s.2∨H' true s.1 s.2);
          (∀ v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
            (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m (A i) (B i) v j|≤err+(m+2)*δ) ∧
          (∀ v,Sum.elim (fun x=>x∈A i) (fun u=>u∈B i) v→∀ j,
            markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
              (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m (A i) (B i) v j=
            markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
              (fun e:KArc=>e.val.1) (fun e=>e.val.2) (Hi true) Finset.univ S m (A i) (B i) v j)) := by
  obtain ⟨M₀,N,hM,hN,hraw⟩ := marked_retained_balance_vortex_event m d hd ε K η χ C Q pstar ζ
    hε hK hη hη1 hχ hpstar hζ
  refine ⟨M₀,N,hM,hN,?_⟩
  intro V U Γ Color W Z _ _ _ _ _ _ _ _ _ _ _ hn hu P π hπ f g ρ hcomm A B M L hL hA hB hstep hAM hBM hInv hW hZ D δP hδP hδε hP p k hp hk hphys q hq hQ s hs hS a j s₀ t₀ ha hj hD0 hDK hratio hmass
  apply (hraw V U Γ Color W Z hn hu P π hπ f g ρ hcomm A B M L hL hA hB hstep hAM hBM hInv hW hZ
    D δP hδP hδε hP p k hp hk hphys q hq hQ s hs hS a j s₀ t₀ ha hj hD0 hDK hratio hmass).trans
  apply finiteLaw_probability_mono
  intro z hz i hi σi Hi E KArc S err
  have hHi : ∀ x u,¬(Hi false x u∧Hi true x u) := by
    intro x u
    exact retainedMarkedSpokes_disjoint π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j (f i x) (g i u)
  have hb := marked_restricted_sample_balance (P.comap (f i)) (ρ i) d m σi Hi hHi (A i) (B i)
    err (by dsimp [err];positivity) (hz i hi)
  refine ⟨hb,?_⟩
  intro KA KS hKS R hEmpty δ hδ hInc
  exact marked_actual_iteration_balance_error (P.comap (f i)) (ρ i) d m σi Hi (A i) (B i)
    (hInv i hi) err δ hδ KA KS hKS hEmpty hInc hb

end Oberwolfach
