module

public import Oberwolfach.MarkedFiniteBalanceAdaptiveVortexEvent
public import Oberwolfach.MarkedFixedVortexInnerDegrees
public import Oberwolfach.MarkedFixedVortexSizes
public import Oberwolfach.MarkedSeedDensities
public import Oberwolfach.MarkedActiveSizeThreshold
public import Oberwolfach.MarkedActiveSeedMass
public import Oberwolfach.VortexSamplingDomainSizes

@[expose] public section
/-! Balance on the actual fixed inner vortex pairs, with a second event on
the same retained law and all later allowed deletions quantified together. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_actual_inner_balance_event
    (c:ℕ) (hc:3≤c) (α ρ₀ sstar tstar epsBal χ Qexp ζ:ℝ)
    (hα:0<α) (hρ₀:0<ρ₀) (hsstar:0<sstar) (htstar:0<tstar)
    (hepsBal:0<epsBal) (hχ:0<χ) (hζ:0<ζ):
    ∃ βmax:ℝ,0<βmax ∧ ∀ ε:ℝ,0<ε→ε≤1/4→∀ (d:ℕ) (hd:2≤d),∃ N₀:ℕ,1≤N₀ ∧
    ∃ m₀:ℕ,1≤m₀ ∧ ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),
    G.IsRegularOfDegree D→∀ (hn:0<Fintype.card V),N₀≤Fintype.card V→
    (1/2+α)*Fintype.card V≤(D:ℝ)→∀ (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1),
    0≤β→β≤βmax→m₀≤m→∀ (π:Equiv.Perm V)
      (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
    (∀ x l,0<l→l<2*d+1→(π^l) x≠x)→∀ L:ℕ,L<Q.length→
    letI : Nonempty V:=Fintype.card_pos_iff.mp hn
    let W:=markedVortexVertexType Q
    letI : ∀ i,DecidableEq (W i):=fun _ a b=>Classical.propDecidable (a=b)
    let Z:=markedVortexHubType Q
    let f:=markedVortexVertexEmbedding Q
    let g:=markedVortexHubEmbedding Q
    let ρ:=markedVortexPermutation Q π hπ
    let A:=markedVortexInnerVertices Q
    let B:=markedVortexInnerHubs Q
    let M:=fun i=>(A i).card
    let Dbal:=fun i=>2*((B i).card:ℝ)/initialIndexDensity U D;
    ∀ (Γ Color:Type) [Fintype Γ] [Fintype Color] (s₀:ℝ) (hslo:sstar≤s₀) (hshi:s₀≤1/100),
    let dens:=initialIndexDensity U D
    let densities:=marked_seed_density_bounds c (by omega) dens s₀ ρ₀ sstar hρ₀ hsstar hρlo hρhi hslo hshi
    let p:=dens*s₀/2
    let kval:=p/(c:ℝ);
    ∀ (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (a:Γ) (j:Color),
      (∀ u,q u a=s₀/c)→(∀ u,s u j=s₀)→tstar≤s₀/c→
    ∀ (Extra:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a→Prop) (extraErr:ℝ),
    1-extraErr≤(rawMarkedRetentionLaw π d hd a p kval (densities.1.trans_le densities.2.1).le
      (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability Extra→
    1-χ-(Fintype.card V:ℝ)^(-Qexp)-extraErr≤
      (rawMarkedRetentionLaw π d hd a p kval (densities.1.trans_le densities.2.1).le
        (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability
      (fun z=>(∀ i≤L,
          let σi := rawMarkedRestrictPair (f i) (g i) z.1
          let Hi := fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u)
          let E := MarkedSampleArc (G.comap (f i)) (ρ i) (3*d) (fun e=>σi (Sum.inl e)) false
          let KArc := MarkedSampleArc (G.comap (f i)) (ρ i) (3*d) (fun e=>σi (Sum.inl e)) true
          let S := Finset.univ.filter (fun s:W i×Z i=>Hi false s.1 s.2∨Hi true s.1 s.2)
          let err := (epsBal+(c+2:ℕ)*ζ)*M i;
          (∀ v j,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
            (fun e:KArc=>e.val.1) (fun e=>e.val.2) (Hi true) Finset.univ S c (A i) (B i) v j|≤err) ∧
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
          let σ' := rawMarkedDeleteRims σi (markedSampleArcSetGraph (G.comap (f i)) (ρ i) d σi KA).edgeFinset
          let H' := markedDeletePhysicalSpokes Hi (markedFiniteSpokeGraph KS)
          let E' := MarkedSampleArc (G.comap (f i)) (ρ i) (3*d) (fun e=>σ' (Sum.inl e)) false
          let K' := MarkedSampleArc (G.comap (f i)) (ρ i) (3*d) (fun e=>σ' (Sum.inl e)) true
          let S' := Finset.univ.filter (fun s:W i×Z i=>H' false s.1 s.2∨H' true s.1 s.2);
          (∀ v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
            (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' c (A i) (B i) v j|≤err+(c+2)*δ) ∧
          (∀ v,Sum.elim (fun x=>x∈A i) (fun u=>u∈B i) v→∀ j,
            markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
              (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' c (A i) (B i) v j=
            markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
              (fun e:KArc=>e.val.1) (fun e=>e.val.2) (Hi true) Finset.univ S c (A i) (B i) v j) ) ∧ Extra z):=by
  let βmax:=min (α/8) (min (1/4) (epsBal/4))
  have hβmax:0<βmax:=by dsimp [βmax];positivity
  refine ⟨βmax,hβmax,?_⟩
  intro ε he he1 d hd
  let K:=2/ε
  let pstar:=ρ₀*tstar/4
  have hK:1≤K:=by dsimp [K];apply (le_div_iff₀ he).2;linarith
  have hpstar:0<pstar:=by dsimp [pstar];positivity
  obtain ⟨M₀,N₀,hM₀,hN₀,hevent⟩:=marked_finite_balance_adaptive_vortex_event c d hd epsBal K (1/2) χ 1 Qexp pstar ζ
    hepsBal hK (by norm_num) (by norm_num) hχ hpstar hζ
  refine ⟨N₀,hN₀,?_⟩
  obtain ⟨m₀,hm₀,hsize⟩:=marked_active_size_threshold ρ₀ ε hρ₀ he M₀ M₀
  refine ⟨m₀,hm₀,?_⟩
  intro V U _ _ _ _ G D m β Q hreg hn hn0 hD hρlo hρhi hb hbmax hm π hπ hshort L hL W Z f g ρ A B M Dbal
  letI : ∀ i,DecidableEq (W i):=fun _ a b=>Classical.propDecidable (a=b)
  have hρ:0 < initialIndexDensity U D:=hρ₀.trans_le hρlo
  have hbα:β≤α/8:=hbmax.trans (min_le_left _ _)
  have hb1:β≤1/4:=hbmax.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbeps:β≤epsBal/4:=hbmax.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hsizeW,_,hsizeB⟩:=hsize m hm
  have hmpos:0<m:=by
    have hp:(0:ℝ)<M₀:=by exact_mod_cast hM₀
    by_contra hh
    have hm0:m=0:=by omega
    rw [hm0] at hsizeW
    simp at hsizeW
    linarith
  have hDhalf:(Fintype.card V:ℝ)/2≤D:=by have hh:(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _;nlinarith
  have hDpos:0<D:=by
    have hn':(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
    exact_mod_cast (lt_of_lt_of_le (by linarith:(0:ℝ)<(Fintype.card V:ℝ)/2) hDhalf)
  have hU:Fintype.card U≤Fintype.card V:=by
    have hh:=Q.index_size_upper hreg hn hDpos he.le hρhi (i:=0) (by omega)
    rw [Q.indices_initial,Q.initial,Finset.card_univ,Finset.card_univ] at hh
    omega
  have hWcard (i:ℕ) (hi:i≤L):Fintype.card (W i)=(Q.vertices i).card:=by
    change Fintype.card (Q.extendedVertices i)=_
    rw [Fintype.card_coe,Q.extendedVertices_eq (hi.trans hL.le)]
  have hZcard (i:ℕ) (hi:i≤L):Fintype.card (Z i)=(Q.indices i).card:=by
    change Fintype.card (Q.extendedIndices i)=_
    rw [Fintype.card_coe,Q.extendedIndices_eq (hi.trans hL.le)]
  have hAcard (i:ℕ) (hi:i≤L):(A i).card=(Q.vertices (i+1)).card:=by
    rw [(marked_vortex_inner_cardinalities Q i).1,Q.extendedVertices_eq (by omega:i+1≤Q.length)]
  have hBcard (i:ℕ) (hi:i≤L):(B i).card=(Q.indices (i+1)).card:=by
    rw [(marked_vortex_inner_cardinalities Q i).2.2.1,Q.extendedIndices_eq (by omega:i+1≤Q.length)]
  have hA (i:ℕ) (hi:i≤L):M₀≤(A i).card:=by
    have hh:=Q.vertices_lower (by omega:i+1≤Q.length)
    have hs:(M₀:ℝ)≤ε*m/2:=by nlinarith
    rw [hAcard i hi]
    exact_mod_cast hs.trans hh
  have hB (i:ℕ) (hi:i≤L):M₀≤(B i).card:=by
    have hh:=Q.vertices_lower (by omega:i+1≤Q.length)
    have hj:=Q.index_size_lower hreg hn hDhalf hρ₀ hρlo hb hb1 (by omega:i+1≤Q.length)
    have hx:=mul_le_mul_of_nonneg_left hh (show 0≤ρ₀/8 by positivity)
    have hs:(M₀:ℝ)≤ρ₀*ε*m/16:=by nlinarith
    rw [hBcard i hi]
    exact_mod_cast (show (M₀:ℝ)≤(Q.indices (i+1)).card by nlinarith)
  have hstep (i:ℕ) (hi:i<L):((M (i+1):ℝ))≤(1/2)*M i:=by
    dsimp [M]
    rw [hAcard (i+1) (by omega),hAcard i (by omega)]
    have hh:((Q.vertices (i+2)).card:ℝ)≤ε*(Q.vertices (i+1)).card:=(Q.consecutive_size_bounds he hmpos (by omega)).2
    nlinarith [Nat.cast_nonneg (α:=ℝ) (Q.vertices (i+1)).card]
  have hAM (i:ℕ) (hi:i≤L):(A i).card≤M i:=le_rfl
  have hBM (i:ℕ) (hi:i≤L):(B i).card≤M i:=by
    dsimp [M]
    rw [hAcard i hi,hBcard i hi]
    have hh:=Q.index_size_upper hreg hn hDpos he.le hρhi (by omega:i+1≤Q.length)
    omega
  have hInv (i:ℕ) (hi:i≤L) (x:W i):ρ i x∈A i↔x∈A i:=
    (marked_vortex_permutation_compatibility Q π hπ i).2.1 x
  have hW (i:ℕ) (hi:i≤L):(Fintype.card (W i):ℝ)≤K*M i:=by
    dsimp [K,M]
    rw [hWcard i hi,hAcard i hi]
    have hh:ε*(Q.vertices i).card/2≤((Q.vertices (i+1)).card:ℝ):=(Q.consecutive_size_bounds he hmpos (by omega)).1
    have haux:((Q.vertices i).card:ℝ)≤(2*(Q.vertices (i+1)).card)/ε:=by
      apply (le_div_iff₀ he).2
      nlinarith
    convert haux using 1 <;> ring
  have hZ (i:ℕ) (hi:i≤L):(Fintype.card (Z i):ℝ)≤K*M i:=by
    have hh:=Q.extended_index_size_upper hreg hn hDpos he.le hρhi i
    rw [Q.extendedIndices_eq (hi.trans hL.le),Q.extendedVertices_eq (hi.trans hL.le),←hZcard i hi,←hWcard i hi] at hh
    have hh':(2:ℝ)*Fintype.card (Z i)≤Fintype.card (W i):=by exact_mod_cast hh
    nlinarith [hW i hi,Nat.cast_nonneg (α:=ℝ) (Fintype.card (Z i))]
  have hnear (i:ℕ) (hi:i≤L) (x:W i):|(((G.comap (f i)).neighborFinset x∩A i).card:ℝ)-Dbal i|≤β*M i:=
    by
      have hh := (marked_vortex_fixed_inner_degree_fields Q hreg hn hD hα hρ hb hbα hb1 he hmpos i (hi.trans_lt hL)).2.1 x
      have heq : (fun a b:W i => Subtype.instDecidableEq a b) = (fun a b:W i => Classical.propDecidable (a=b)) := Subsingleton.elim _ _
      rw [heq] at hh
      exact hh
  intro Γ Color _ _ s₀ hslo hshi dens densities p kval q hq hQ s hs hS a j hq0 hs0 htlo Extra extraErr hExtra
  letI : Nonempty V:=Fintype.card_pos_iff.mp hn
  have hLsize:(L+1:ℝ)≤(Fintype.card V:ℝ)^(1:ℝ):=by
    have hh:L+1≤Fintype.card V:=le_trans (Nat.add_le_add_right hL.le 1) (Q.number_of_levels_le_order he (by linarith) hmpos)
    simpa only [Real.rpow_one] using (show (L+1:ℝ)≤Fintype.card V by exact_mod_cast hh)
  have hbalance (i:ℕ) (hi:i≤L):p*Dbal i=s₀*(B i).card ∧ kval*Dbal i=(s₀/c)*(B i).card:=by
    have hh:=marked_seed_density_balance c (by omega) dens s₀ ((B i).card) hρ.ne'
    constructor <;> dsimp [p,kval,Dbal,dens] at hh ⊢ <;> field_simp <;> ring
  have hmass:pstar*Fintype.card V≤(s₀/c)*Fintype.card U:=
    marked_active_seed_mass_bound D ρ₀ tstar (s₀/c) pstar hρ₀ htstar hn hDhalf hρlo htlo (by dsimp [pstar];rfl)
  have hp:0<p:=densities.1.trans_le densities.2.1
  have hk:0<kval:=densities.1.trans_le densities.2.2.1
  have hphys:2*p+2*kval≤1:=densities.2.2.2.2.2.2.2.2
  have hc0:(c:ℝ)≠0:=by exact_mod_cast (show c≠0 by omega)
  have hratio:s₀=(c:ℝ)*(s₀/c):=by field_simp [hc0]
  have hh:=hevent V U Γ Color W Z hn0 hU G π hshort f g ρ
    (fun i x=>(marked_vortex_permutation_compatibility Q π hπ i).1 x) A B M L hLsize hA hB hstep hAM hBM hInv hW hZ
    Dbal β hb hbeps (by
      intro i hi x
      have hh:=hnear i hi x
      exact hh) p kval hp.le hk.le hphys q hq hQ s hs hS a j s₀ (s₀/c) hq0 hs0
    (fun i hi=>(hbalance i hi).1) (fun i hi=>(hbalance i hi).2) hratio
    hmass
  let μ:=rawMarkedRetentionLaw π d hd a p kval hp.le hk.le hphys q hq hQ s hs hS
  let EBal:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a=>
    ∀ i≤L,
          let σi := rawMarkedRestrictPair (f i) (g i) z.1
          let Hi := fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u)
          let E := MarkedSampleArc (G.comap (f i)) (ρ i) (3*d) (fun e=>σi (Sum.inl e)) false
          let KArc := MarkedSampleArc (G.comap (f i)) (ρ i) (3*d) (fun e=>σi (Sum.inl e)) true
          let S := Finset.univ.filter (fun s:W i×Z i=>Hi false s.1 s.2∨Hi true s.1 s.2)
          let err := (epsBal+(c+2:ℕ)*ζ)*M i;
          (∀ v j,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
            (fun e:KArc=>e.val.1) (fun e=>e.val.2) (Hi true) Finset.univ S c (A i) (B i) v j|≤err) ∧
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
          let σ' := rawMarkedDeleteRims σi (markedSampleArcSetGraph (G.comap (f i)) (ρ i) d σi KA).edgeFinset
          let H' := markedDeletePhysicalSpokes Hi (markedFiniteSpokeGraph KS)
          let E' := MarkedSampleArc (G.comap (f i)) (ρ i) (3*d) (fun e=>σ' (Sum.inl e)) false
          let K' := MarkedSampleArc (G.comap (f i)) (ρ i) (3*d) (fun e=>σ' (Sum.inl e)) true
          let S' := Finset.univ.filter (fun s:W i×Z i=>H' false s.1 s.2∨H' true s.1 s.2);
          (∀ v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
            (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' c (A i) (B i) v j|≤err+(c+2)*δ) ∧
          (∀ v,Sum.elim (fun x=>x∈A i) (fun u=>u∈B i) v→∀ j,
            markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
              (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' c (A i) (B i) v j=
            markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
              (fun e:KArc=>e.val.1) (fun e=>e.val.2) (Hi true) Finset.univ S c (A i) (B i) v j)
  have hbase:1-χ-(Fintype.card V:ℝ)^(-Qexp)≤μ.probability EBal:=by simpa only [μ,EBal] using hh
  have hjoin:=finiteLaw_good_intersection μ EBal Extra extraErr hExtra
  change 1-χ-(Fintype.card V:ℝ)^(-Qexp)-extraErr≤μ.probability (fun z=>EBal z ∧ Extra z)
  linarith
end Oberwolfach
