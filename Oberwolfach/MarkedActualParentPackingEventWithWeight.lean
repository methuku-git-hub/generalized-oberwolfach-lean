module

public import Oberwolfach.MarkedFixedVortexSuccessorWeights
public import Oberwolfach.MarkedPackingAdaptiveVortexEvent
public import Oberwolfach.MarkedSeedDensities
public import Oberwolfach.MarkedActiveSizeThreshold
public import Oberwolfach.MarkedActiveSeedMass
public import Oberwolfach.VortexSamplingDomainSizes

@[expose] public section
/-! Parent packing loads on all levels of the actual fixed vortex, with a
second event on the same retained law and weights chosen before sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_actual_parent_packing_event_with_weight
    (k₀ c:ℕ) (hlen:c+1=(k₀+2)*2) (hc:3≤c)
    (α τ ρ₀ sstar tstar tol χ Qexp ζ:ℝ)
    (hα:0<α) (hτ:0<τ) (hρ₀:0<ρ₀) (hsstar:0<sstar) (htstar:0<tstar)
    (htol:0<tol) (hχ:0<χ) (hζ:0<ζ)
    (hmargin:successorCycleRatio k₀+α/4≤1/2+α/2):
    ∃ βmax:ℝ,0<βmax ∧ ∀ (d:ℕ) (hd:2≤d),∃ N₀:ℕ,1≤N₀ ∧
    ∀ ε:ℝ,0<ε→ε≤1/4→∃ m₀:ℕ,1≤m₀ ∧
    ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),
    G.IsRegularOfDegree D→∀ (hn:0<Fintype.card V),N₀≤Fintype.card V→
    (1/2+α)*Fintype.card V≤(D:ℝ)→∀ (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1),
    0≤β→β≤βmax→m₀≤m→∀ (π:Equiv.Perm V)
      (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
    (∀ x l,0<l→l<2*d+1→(π^l) x≠x)→∀ L:ℕ,L<Q.length→
    letI : Nonempty V:=Fintype.card_pos_iff.mp hn
    let W:=markedVortexVertexType Q
    let Z:=markedVortexHubType Q
    let f:=markedVortexVertexEmbedding Q
    let g:=markedVortexHubEmbedding Q
    let ρ:=markedVortexPermutation Q π hπ
    let Dload:=fun i=>2*(Fintype.card (Z i):ℝ)/initialIndexDensity U D
    let pstar:=ρ₀*sstar/(2*(c:ℝ));
    ∃ weight:∀ i,(Fin (c+1)→W i)→ℝ,
    (∀ i≤L,SuccessorSequenceWeightConditions (G.comap (f i)) (ρ i) (3*d)
      (Dload i) τ (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weight i)) ∧
    ∀ (Γ Color:Type) [Fintype Γ] [Fintype Color] (s₀:ℝ) (hslo:sstar≤s₀) (hshi:s₀≤1/100),
    let dens:=initialIndexDensity U D
    let densities:=marked_seed_density_bounds c (by omega) dens s₀ ρ₀ sstar hρ₀ hsstar hρlo hρhi hslo hshi
    let p:=dens*s₀/2
    let kval:=p/(c:ℝ);
    ∀ (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (a:Γ) (j:Color),
      (∀ u,q u a=s₀/c)→(∀ u,s u j=s₀)→tstar≤s₀/c→
    ∀ (E:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a→Prop) (err:ℝ),
    1-err≤(rawMarkedRetentionLaw π d hd a p kval (densities.1.trans_le densities.2.1).le
      (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability E→
    1-χ-(Fintype.card V:ℝ)^(-Qexp)-err≤
      (rawMarkedRetentionLaw π d hd a p kval (densities.1.trans_le densities.2.1).le
        (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability
      (fun z=>(∀ i≤L,∀ δ:ℝ,0≤δ→∀ (DR:SimpleGraph (W i)) (DS:SimpleGraph (W i⊕Z i)),
        (∀ x,(DR.degree x:ℝ)≤δ)→(∀ x,(DS.degree x:ℝ)≤δ)→
        MarkedPackingLoadsWithSpokes (G.comap (f i)) (ρ i) d c (Dload i) p kval s₀ (weight i) a j
          (Function.Embedding.refl (Z i)) (fun u=>q (g i u)) (fun u=>s (g i u))
          (τ+tol+11*((c:ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstar^(2*c+1))*ζ+
            33*((c:ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstar^(2*c+1))*δ/Fintype.card (W i))
          (rawMarkedDeleteRims (rawMarkedRestrictPair (f i) (g i) z.1) DR.edgeFinset)
          (markedDeletePhysicalSpokes
            (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
              (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u)) DS)) ∧ E z):=by
  let pstar:=ρ₀*sstar/(2*(c:ℝ))
  let pret:=ρ₀*tstar/4
  have hpstar:0<pstar:=by dsimp [pstar];positivity
  have hpret:0<pret:=by dsimp [pret];positivity
  have hUpper:0<successorWeightUpper k₀ (α/4):=(successorWeightConstants_pos k₀ (α/4) (by positivity)).2
  obtain ⟨βbase,hβbase,hweights⟩:=marked_fixed_vortex_successor_weight_families k₀ c hlen α τ hα hτ hmargin
  let βmax:=min βbase (min (α/8) (1/4))
  have hβmax:0<βmax:=by dsimp [βmax];positivity
  refine ⟨βmax,hβmax,?_⟩
  intro d hd
  obtain ⟨Nweight,hNweight,hweights⟩:=hweights (3*d)
  obtain ⟨M₀,N₀,hM₀,hN₀,hevent⟩:=marked_packing_adaptive_vortex_event c d hc hd
    (successorWeightUpper k₀ (α/4)) pstar tol 1 (1/2) χ 1 Qexp pret ζ
    hUpper hpstar htol (by norm_num) (by norm_num) (by norm_num) hχ hpret hζ
  refine ⟨N₀,hN₀,?_⟩
  intro ε he he1
  obtain ⟨m₀,hm₀,hsize⟩:=marked_active_size_threshold ρ₀ ε hρ₀ he M₀ Nweight
  refine ⟨m₀,hm₀,?_⟩
  intro V U _ _ _ _ G D m β Q hreg hn hn0 hD hρlo hρhi hb hbmax hm π hπ hshort L hL W Z f g ρ Dload pstar'
  have hρ:0 < initialIndexDensity U D:=hρ₀.trans_le hρlo
  have hbbase:β≤βbase:=hbmax.trans (min_le_left _ _)
  have hbα:β≤α/8:=hbmax.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hb1:β≤1/4:=hbmax.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hsizeW,hsizeA,hsizeB⟩:=hsize m hm
  have hmpos:0<m:=by
    have hp:(0:ℝ)<Nweight:=by exact_mod_cast hNweight
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
  have hwsize:(Nweight:ℝ)≤ε*m/2:=by nlinarith
  obtain ⟨weight,hweight⟩:=hweights V U G D m β ε Q hreg hn hD hρ hb hbbase he hwsize π hπ L hL
  refine ⟨weight,hweight,?_⟩
  intro Γ Color _ _ s₀ hslo hshi dens densities p kval q hq hQ s hs hS a j hq0 hs0 htlo E err hExtra
  letI : Nonempty V:=Fintype.card_pos_iff.mp hn
  have hLsize:(L+1:ℝ)≤(Fintype.card V:ℝ)^(1:ℝ):=by
    have hh:L+1≤Fintype.card V:=le_trans (Nat.add_le_add_right hL.le 1) (Q.number_of_levels_le_order he (by linarith) hmpos)
    simpa only [Real.rpow_one] using (show (L+1:ℝ)≤Fintype.card V by exact_mod_cast hh)
  have hWcard (i:ℕ) (hi:i≤L):Fintype.card (W i)=(Q.vertices i).card:=by
    change Fintype.card (Q.extendedVertices i)=_
    rw [Fintype.card_coe,Q.extendedVertices_eq (hi.trans hL.le)]
  have hZcard (i:ℕ) (hi:i≤L):Fintype.card (Z i)=(Q.indices i).card:=by
    change Fintype.card (Q.extendedIndices i)=_
    rw [Fintype.card_coe,Q.extendedIndices_eq (hi.trans hL.le)]
  have hW (i:ℕ) (hi:i≤L):M₀≤Fintype.card (W i):=by
    have hh:=Q.vertices_lower (hi.trans hL.le)
    have hsize:(M₀:ℝ)≤ε*m/2:=by nlinarith
    rw [hWcard i hi]
    exact_mod_cast hsize.trans hh
  have hZ (i:ℕ) (hi:i≤L):M₀≤Fintype.card (Z i):=by
    have hh:=Q.vertices_lower (hi.trans hL.le)
    have hj:=Q.index_size_lower hreg hn hDhalf hρ₀ hρlo hb hb1 (hi.trans hL.le)
    have hx:=mul_le_mul_of_nonneg_left hh (show 0≤ρ₀/8 by positivity)
    have hsize:(M₀:ℝ)≤ρ₀*ε*m/16:=by nlinarith
    rw [hZcard i hi]
    exact_mod_cast (show (M₀:ℝ)≤(Q.indices i).card by nlinarith)
  have hstep (i:ℕ) (hi:i<L):(Fintype.card (W (i+1)):ℝ)≤(1/2)*Fintype.card (W i):=by
    have hh:((Q.vertices (i+1)).card:ℝ)≤ε*(Q.vertices i).card:=(Q.consecutive_size_bounds he hmpos (by omega)).2
    rw [hWcard (i+1) (by omega),hWcard i (by omega)]
    nlinarith [Nat.cast_nonneg (α:=ℝ) (Q.vertices i).card]
  have hZW (i:ℕ) (hi:i≤L):(Fintype.card (Z i):ℝ)≤1*Fintype.card (W i):=by
    have hh:=Q.extended_index_size_upper hreg hn hDpos he.le hρhi i
    rw [Q.extendedIndices_eq (hi.trans hL.le),Q.extendedVertices_eq (hi.trans hL.le),←hZcard i hi,←hWcard i hi] at hh
    have hh':(2:ℝ)*Fintype.card (Z i)≤Fintype.card (W i):=by exact_mod_cast hh
    nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card (Z i))]
  have hHW (i:ℕ) (hi:i≤L):Fintype.card (Z i)≤Fintype.card (W i):=by
    have hh:=hZW i hi
    simp only [one_mul] at hh
    exact_mod_cast hh
  have hfields (i:ℕ) (hi:i≤L):=marked_vortex_fixed_parent_degree_fields Q hreg hn hD hα hρ hb hbα hb1 he hmpos i (hi.trans_lt hL)
  have hDlo (i:ℕ) (hi:i≤L):(Fintype.card (W i):ℝ)/2≤Dload i:=(hfields i hi).2.2.1
  have hDhi (i:ℕ) (hi:i≤L):Dload i≤2*Fintype.card (W i):=(hfields i hi).2.2.2
  have hmarked (i:ℕ) (hi:i≤L):(Fintype.card (Z i):ℝ)*(s₀/c)=Dload i*kval:=by
    have hh:=marked_seed_density_balance c (by omega) dens s₀ (Fintype.card (Z i)) hρ.ne'
    exact hh.1
  have hord (i:ℕ) (hi:i≤L):(Fintype.card (Z i):ℝ)*(s₀/c)*c=Dload i*p:=by
    have hh:=marked_seed_density_balance c (by omega) dens s₀ (Fintype.card (Z i)) hρ.ne'
    exact hh.2
  have hp:0<p:=densities.1.trans_le densities.2.1
  have hk:0<kval:=densities.1.trans_le densities.2.2.1
  have hphys:2*p+2*kval≤1:=densities.2.2.2.2.2.2.2.2
  have hmass:pret*Fintype.card V≤(s₀/c)*Fintype.card U:=
    marked_active_seed_mass_bound D ρ₀ tstar (s₀/c) pret hρ₀ htstar hn hDhalf hρlo htlo (by dsimp [pret];rfl)
  have hh:=hevent V U Γ Color W Z Z hn0 hU G π hshort f g (fun i=>Function.Embedding.refl (Z i)) ρ
    (fun i x=>(marked_vortex_permutation_compatibility Q π hπ i).1 x) L hLsize hW hZ hstep hZW hHW
    Dload τ (successorWeightLower k₀ (α/4)) hDlo hDhi weight hweight
    p kval s₀ hp hk hphys densities.2.1 densities.2.2.1 densities.2.2.2.1
    densities.2.2.2.2.1 densities.2.2.2.2.2.1 densities.2.2.2.2.2.2.1
    hmarked hord q hq hQ s hs hS a j hq0 hs0 hmass
  let μ:=rawMarkedRetentionLaw π d hd a p kval hp.le hk.le hphys q hq hQ s hs hS
  let PParent:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a=>
    ∀ i≤L,∀ δ:ℝ,0≤δ→∀ (DR:SimpleGraph (W i)) (DS:SimpleGraph (W i⊕Z i)),
      (∀ x,(DR.degree x:ℝ)≤δ)→(∀ x,(DS.degree x:ℝ)≤δ)→
      MarkedPackingLoadsWithSpokes (G.comap (f i)) (ρ i) d c (Dload i) p kval s₀ (weight i) a j
        (Function.Embedding.refl (Z i)) (fun u=>q (g i u)) (fun u=>s (g i u))
        (τ+tol+11*((c:ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstar^(2*c+1))*ζ+
          33*((c:ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstar^(2*c+1))*δ/Fintype.card (W i))
        (rawMarkedDeleteRims (rawMarkedRestrictPair (f i) (g i) z.1) DR.edgeFinset)
        (markedDeletePhysicalSpokes
          (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u)) DS)
  have hbase:1-χ-(Fintype.card V:ℝ)^(-Qexp)≤μ.probability PParent:=by
    simpa only [μ,PParent,one_mul,mul_one] using hh
  have hjoin:=finiteLaw_good_intersection μ PParent E err hExtra
  change 1-χ-(Fintype.card V:ℝ)^(-Qexp)-err≤μ.probability (fun z=>PParent z ∧ E z)
  linarith
end Oberwolfach
