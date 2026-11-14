module

public import Oberwolfach.MarkedVortexActualActiveInputs
public import Oberwolfach.MarkedNestedVortexActiveGeometry
public import Oberwolfach.MarkedRetainedLocalLoadVortex
public import Oberwolfach.VortexSamplingDomainSizes

@[expose] public section
/-! Retained local spoke loads on the actual fixed active vortex sets. The
weights are chosen before the profile and the two exposures. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_actual_active_local_load_event
    (k c:ℕ) (hlen:c+1=(k+2)*2) (hc:3≤c)
    (α τ ρ₀ pstar tol χ Qexp pret ζ:ℝ)
    (hα:0<α) (hτ:0<τ) (hρ₀:0<ρ₀) (hpstar:0<pstar)
    (htol:0<tol) (hχ:0<χ) (hpret:0<pret) (hζ:0<ζ)
    (hmargin:successorCycleRatio k+α/4≤1/2+α/2):
    ∃ βmax:ℝ,0<βmax ∧ ∀ (d:ℕ) (hd:2≤d),∃ M₀ N₀ Nweight:ℕ,1≤M₀ ∧ 1≤N₀ ∧ 1≤Nweight ∧
    ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m),
    G.IsRegularOfDegree D→∀ (hn:0<Fintype.card V),N₀≤Fintype.card V→
    (1/2+α)*Fintype.card V≤(D:ℝ)→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→
    0≤β→β≤βmax→0<ε→ε≤1/4→
    (Nweight:ℝ)≤3*ε*m/8→(M₀:ℝ)≤3*ε*m/8→(M₀:ℝ)≤9*ρ₀*ε*m/256→
    ∀ (π:Equiv.Perm V) (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
    (∀ x l,0<l→l<2*d+1→(π^l) x≠x)→∀ L:ℕ,L≤Q.length→
    letI : Nonempty V:=Fintype.card_pos_iff.mp hn
    let W:=fun i=>markedVortexVertexType Q i
    let Z:=fun i=>markedVortexHubType Q i
    let A:∀ i,Finset (W i):=fun i=>Finset.univ\markedVortexInnerVertices Q i
    let B:∀ i,Finset (Z i):=fun i=>Finset.univ\markedVortexInnerHubs Q i
    let X:=fun i=>↥(A i)
    let Y:=fun i=>↥(B i)
    let f:=fun i=>markedVortexActiveVertexEmbedding Q i
    let g:=fun i=>markedVortexActiveHubEmbedding Q i
    let ρ:=fun i=>markedVortexActivePermutation Q π hπ i
    let Dactive:=fun i=>2*((B i).card:ℝ)/initialIndexDensity U D;
    ∃ weight:∀ i,(Fin (c+1)→X i)→ℝ,
    ∀ (Γ Color:Type) [Fintype Γ] [Fintype Color]
      (p kval s₀:ℝ) (hp:0<p) (hk:0<kval) (hphys:2*p+2*kval≤1),
      pstar≤p→pstar≤kval→pstar≤s₀→p≤1→kval≤1→s₀≤1→
    ∀ (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (a:Γ) (j:Color),
      (∀ u,q u a=s₀/c)→(∀ u,s u j=s₀)→pret*Fintype.card V≤(s₀/c)*Fintype.card U→
    ∀ (E:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a→Prop) (err:ℝ),
    1-err≤(rawMarkedRetentionLaw π d hd a p kval hp.le hk.le hphys q hq hQ s hs hS).probability E→
    1-χ-(Fintype.card V:ℝ)^(-Qexp)-err≤
      (rawMarkedRetentionLaw π d hd a p kval hp.le hk.le hphys q hq hQ s hs hS).probability
        (fun z=>(∀ i≤L,MarkedLocalSpokeLoadsWithSpokes (G.comap (f i)) (ρ i) d c (Dactive i) p kval s₀ (weight i)
          (τ+tol+5*((c:ℝ)+1)^4*(2*successorWeightUpper k (α/4)/pstar^(2*c+1))*ζ)
          (rawMarkedRestrictPair (f i) (g i) z.1)
          (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u))) ∧ E z):=by
  have hUpper:0<successorWeightUpper k (α/4):=(successorWeightConstants_pos k (α/4) (by positivity)).2
  obtain ⟨βbase,hβbase,hweights⟩:=marked_vortex_actual_active_inputs k c hlen α τ hα hτ hmargin
  let βmax:=min βbase (1/4)
  have hβmax:0<βmax:=by dsimp [βmax];positivity
  refine ⟨βmax,hβmax,?_⟩
  intro d hd
  obtain ⟨Nweight,hNweight,hweights⟩:=hweights (3*d)
  obtain ⟨M₀,N₀,hM₀,hN₀,hevent⟩:=marked_retained_local_load_vortex_event c d hc hd
    (successorWeightUpper k (α/4)) pstar tol 1 (1/2) χ 1 Qexp pret ζ
    hUpper hpstar htol (by norm_num) (by norm_num) (by norm_num) hχ hpret hζ
  refine ⟨M₀,N₀,Nweight,hM₀,hN₀,hNweight,?_⟩
  intro V U _ _ _ _ G D m β ε Q hreg hn hn0 hD hρlo hρhi hb hbmax he he1 hsizeW hsizeA hsizeB π hπ hshort L hL W Z A B X Y f g ρ Dactive
  have hρ:0 < initialIndexDensity U D:=hρ₀.trans_le hρlo
  have hbbase:β≤βbase:=hbmax.trans (min_le_left _ _)
  have hb1:β≤1/4:=hbmax.trans (min_le_right _ _)
  have hDhalf:(Fintype.card V:ℝ)/2≤D:=by
    have hn':(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _
    nlinarith
  have hDpos:0<D:=by
    have hn':(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
    exact_mod_cast (lt_of_lt_of_le (by linarith:(0:ℝ)<(Fintype.card V:ℝ)/2) hDhalf)
  have hm:0<m:=by
    by_contra hm
    have hm0:m=0:=by omega
    rw [hm0] at hsizeW
    have hp:(0:ℝ)<Nweight:=by exact_mod_cast hNweight
    simp at hsizeW
    linarith
  have hU:Fintype.card U≤Fintype.card V:=by
    have hh:=Q.index_size_upper hreg hn hDpos he.le hρhi (i:=0) (by omega)
    rw [Q.indices_initial,Q.initial,Finset.card_univ,Finset.card_univ] at hh
    omega
  have hgeom (i:ℕ) (hi:i≤L):=marked_nested_vortex_active_geometry Q ρ₀ hρ₀ hreg hn hDhalf hρlo hρhi hb hb1 he.le he1 i (hi.trans hL)
  have hW (i:ℕ) (hi:i≤L):M₀≤Fintype.card (X i):=by
    have hh:=hsizeA.trans (hgeom i hi).2.2.2.1
    rw [Fintype.card_coe]
    exact_mod_cast hh
  have hZ (i:ℕ) (hi:i≤L):M₀≤Fintype.card (Y i):=by
    have hh:=hsizeB.trans (hgeom i hi).2.2.2.2
    rw [Fintype.card_coe]
    exact_mod_cast hh
  obtain ⟨weight,hinput⟩:=hweights V U G D m β ε Q hreg hn hD hρ hb hbbase he he1 hsizeW π hπ L hL
  refine ⟨weight,?_⟩
  intro Γ Color _ _ p kval s₀ hp hk hphys hp0 hk0 hsbound hp1 hk1 hs1 q hq hQ s hs hS a j hq0 hsprofile hmass E err hExtra
  letI : Nonempty V:=Fintype.card_pos_iff.mp hn
  have hLsize:(L+1:ℝ)≤(Fintype.card V:ℝ)^(1:ℝ):=by
    have hh: L+1≤Fintype.card V:=le_trans (Nat.add_le_add_right hL 1) (Q.number_of_levels_le_order he (by linarith) hm)
    simpa only [Real.rpow_one] using (show (L+1:ℝ)≤Fintype.card V by exact_mod_cast hh)
  have hdec (i:ℕ) (hi:i<L):(Fintype.card (X (i+1)):ℝ)≤(1/2)*Fintype.card (X i):=by
    have hh:(((A (i+1)).card):ℝ)≤(4*ε/3)*(A i).card:=(hgeom i (by omega)).2.2.1
    have ha:(0:ℝ)≤(A i).card:=Nat.cast_nonneg _
    rw [Fintype.card_coe,Fintype.card_coe]
    nlinarith
  have hZW (i:ℕ) (hi:i≤L):(Fintype.card (Y i):ℝ)≤1*Fintype.card (X i):=by
    have hh:= (hgeom i hi).2.1
    rw [Fintype.card_coe,Fintype.card_coe]
    have ha:(0:ℝ)≤(A i).card:=Nat.cast_nonneg _
    nlinarith
  have hDlo (i:ℕ) (hi:i≤L):(Fintype.card (X i):ℝ)/2≤Dactive i:=by
    let x:X i:=Classical.choice (Fintype.card_pos_iff.mp (by have hh:=hW i hi;omega))
    have hh:=(hinput i hi).2.1 x
    rw [Fintype.card_coe]
    exact hh.1
  have hDhi (i:ℕ) (hi:i≤L):Dactive i≤2*Fintype.card (X i):=by
    let x:X i:=Classical.choice (Fintype.card_pos_iff.mp (by have hh:=hW i hi;omega))
    have hh:=(hinput i hi).2.1 x
    rw [Fintype.card_coe]
    exact hh.2.1
  have hw (i:ℕ) (hi:i≤L):SuccessorSequenceWeightConditions (G.comap (f i)) (ρ i) (3*d)
      (Dactive i) τ (successorWeightLower k (α/4)) (successorWeightUpper k (α/4)) (weight i):=by
    exact (hinput i hi).1
  have hh:=hevent V U Γ Color X Y hn0 hU G π hshort f g ρ
    (fun i x=>marked_vortex_active_permutation_embedding Q π hπ i x) L hLsize hW hZ hdec hZW
    Dactive τ (successorWeightLower k (α/4)) hDlo hDhi weight hw
    p kval s₀ hp hk hphys hp0 hk0 hsbound hp1 hk1 hs1 q hq hQ s hs hS a j hq0 hsprofile hmass
  let μ:=rawMarkedRetentionLaw π d hd a p kval hp.le hk.le hphys q hq hQ s hs hS
  let PLocal:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a=>
    ∀ i≤L,MarkedLocalSpokeLoadsWithSpokes (G.comap (f i)) (ρ i) d c (Dactive i) p kval s₀ (weight i)
      (τ+tol+5*((c:ℝ)+1)^4*(2*successorWeightUpper k (α/4)/pstar^(2*c+1))*ζ)
      (rawMarkedRestrictPair (f i) (g i) z.1)
      (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u))
  have hbase:1-χ-(Fintype.card V:ℝ)^(-Qexp)≤μ.probability PLocal:=by
    simpa only [μ,PLocal,one_mul,mul_one] using hh
  have hjoin:=finiteLaw_good_intersection μ PLocal E err hExtra
  change 1-χ-(Fintype.card V:ℝ)^(-Qexp)-err≤μ.probability (fun z=>PLocal z ∧ E z)
  linarith
end Oberwolfach
