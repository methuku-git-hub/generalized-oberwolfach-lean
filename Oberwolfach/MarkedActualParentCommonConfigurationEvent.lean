module

public import Oberwolfach.MarkedRetainedCommonConfigurationVortex
public import Oberwolfach.MarkedFixedVortexParentDegrees
public import Oberwolfach.MarkedSeedDensities
public import Oberwolfach.MarkedActiveSizeThreshold
public import Oberwolfach.MarkedActiveSeedMass
public import Oberwolfach.VortexSamplingDomainSizes

@[expose] public section
/-! Retained common configuration estimates on the actual fixed parent vortex levels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_actual_parent_common_configuration_event
    (r c:ℕ) (hr:1≤r) (hc:3≤c) (α ρ₀ sstar tstar kstar χ Qexp:ℝ)
    (hα:0<α) (hα1:α≤1) (hρ₀:0<ρ₀) (hsstar:0<sstar) (htstar:0<tstar) (htstar1:tstar≤1)
    (hkstar:0<kstar) (hχ:0<χ):
    ∃ βCommon βmax:ℝ,0<βCommon ∧ 0<βmax ∧ ∀ ζ:ℝ,0<ζ→∀ (d:ℕ) (hd:2≤d),∃ N₀:ℕ,1≤N₀ ∧
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
    let ρ:=markedVortexPermutation Q π hπ;
    ∀ (Γ Color:Type) [Fintype Γ] [Fintype Color] (s₀:ℝ) (hslo:sstar≤s₀) (hshi:s₀≤1/100),
    let dens:=initialIndexDensity U D
    let densities:=marked_seed_density_bounds c (by omega) dens s₀ ρ₀ sstar hρ₀ hsstar hρlo hρhi hslo hshi
    let p:=dens*s₀/2
    let kval:=p/(c:ℝ);
    kstar≤p→kstar≤kval→
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
      (fun z=>(∀ i≤L,MarkedCommonConfigurationsWithSpokes r (G.comap (f i)) (ρ i) d βCommon ζ
        (rawMarkedRestrictPair (f i) (g i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u))) ∧ Extra z):=by
  obtain ⟨βCommon,hβCommon,hcommon⟩:=marked_retained_common_configurations_vortex_event r hr (α/2) sstar tstar kstar (ρ₀/8)
    (by positivity) (by linarith) hsstar htstar hkstar (by positivity)
  let βmax:=min (α/8) (1/4)
  have hβmax:0<βmax:=by dsimp [βmax];positivity
  refine ⟨βCommon,βmax,hβCommon,hβmax,?_⟩
  intro ζ hζ d hd
  let pstar:=ρ₀*tstar/4
  have hpstar:0<pstar:=by dsimp [pstar];positivity
  obtain ⟨M₀,N₀,hM₀,hN₀,hevent⟩:=hcommon (1/2) χ 1 Qexp pstar ζ (by norm_num) (by norm_num) hχ hpstar hζ d hd
  refine ⟨N₀,hN₀,?_⟩
  intro ε he he1
  obtain ⟨m₀,hm₀,hsize⟩:=marked_active_size_threshold ρ₀ ε hρ₀ he M₀ M₀
  refine ⟨m₀,hm₀,?_⟩
  intro V U _ _ _ _ G D m β Q hreg hn hn0 hD hρlo hρhi hb hbmax hm π hπ hshort L hL W Z f g ρ
  letI : Nonempty V:=Fintype.card_pos_iff.mp hn
  have hρ:0< initialIndexDensity U D:=hρ₀.trans_le hρlo
  have hbα:β≤α/8:=hbmax.trans (min_le_left _ _)
  have hb1:β≤1/4:=hbmax.trans (min_le_right _ _)
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
    rw [Fintype.card_coe,Q.extendedVertices_eq (by omega:i≤Q.length)]
  have hZcard (i:ℕ) (hi:i≤L):Fintype.card (Z i)=(Q.indices i).card:=by
    change Fintype.card (Q.extendedIndices i)=_
    rw [Fintype.card_coe,Q.extendedIndices_eq (by omega:i≤Q.length)]
  have hW (i:ℕ) (hi:i≤L):M₀≤Fintype.card (W i):=by
    have hh:=Q.vertices_lower (by omega:i≤Q.length)
    have hs:(M₀:ℝ)≤ε*m/2:=by nlinarith
    rw [hWcard i hi]
    exact_mod_cast hs.trans hh
  have hZ (i:ℕ) (hi:i≤L):M₀≤Fintype.card (Z i):=by
    have hh:=Q.vertices_lower (by omega:i≤Q.length)
    have hj:=Q.index_size_lower hreg hn hDhalf hρ₀ hρlo hb hb1 (by omega:i≤Q.length)
    have hx:=mul_le_mul_of_nonneg_left hh (show 0≤ρ₀/8 by positivity)
    have hs:(M₀:ℝ)≤ρ₀*ε*m/16:=by nlinarith
    rw [hZcard i hi]
    exact_mod_cast (show (M₀:ℝ)≤(Q.indices i).card by nlinarith)
  have hstep (i:ℕ) (hi:i<L):((Fintype.card (W (i+1)):ℝ))≤(1/2)*Fintype.card (W i):=by
    rw [hWcard (i+1) (by omega),hWcard i (by omega)]
    have hh:((Q.vertices (i+1)).card:ℝ)≤ε*(Q.vertices i).card:=(Q.consecutive_size_bounds he hmpos (by omega)).2
    nlinarith [Nat.cast_nonneg (α:=ℝ) (Q.vertices i).card]
  have hzlo (i:ℕ) (hi:i≤L):(ρ₀/8)*Fintype.card (W i)≤(Fintype.card (Z i):ℝ):=by
    rw [hWcard i hi,hZcard i hi]
    exact Q.index_size_lower hreg hn hDhalf hρ₀ hρlo hb hb1 (by omega:i≤Q.length)
  have hzhi (i:ℕ) (hi:i≤L):Fintype.card (Z i)≤Fintype.card (W i):=by
    rw [hWcard i hi,hZcard i hi]
    have hh:=Q.index_size_upper hreg hn hDpos he.le hρhi (by omega:i≤Q.length)
    omega
  have hmin (i:ℕ) (hi:i≤L) (x:W i):(1/2+α/2)*Fintype.card (W i)≤((G.comap (f i)).degree x:ℝ):=
    (marked_vortex_fixed_parent_degree_fields Q hreg hn hD hα hρ hb hbα hb1 he hmpos i (by omega)).1 x
  intro Γ Color _ _ s₀ hslo hshi dens densities p kval hpmin hkmin q hq hQ s hs hS a j hq0 hs0 htlo Extra extraErr hExtra
  have hLsize:(L+1:ℝ)≤(Fintype.card V:ℝ)^(1:ℝ):=by
    have hh:L+1≤Fintype.card V:=le_trans (Nat.add_le_add_right hL.le 1) (Q.number_of_levels_le_order he (by linarith) hmpos)
    simpa only [Real.rpow_one] using (show (L+1:ℝ)≤Fintype.card V by exact_mod_cast hh)
  have hmass:pstar*Fintype.card V≤(s₀/c)*Fintype.card U:=
    marked_active_seed_mass_bound D ρ₀ tstar (s₀/c) pstar hρ₀ htstar hn hDhalf hρlo htlo (by dsimp [pstar];rfl)
  have htS:tstar≤s₀:=by
    have hc0:(1:ℝ)≤c:=by exact_mod_cast (show 1≤c by omega)
    have hs0:0≤s₀:=hsstar.le.trans hslo
    have hcpos:0<(c:ℝ):=lt_of_lt_of_le (by norm_num) hc0
    have hh:s₀/c≤s₀:=by apply (div_le_iff₀ hcpos).2;nlinarith
    exact htlo.trans hh
  have hp:=densities.1.trans_le densities.2.1
  have hk:=densities.1.trans_le densities.2.2.1
  have hphys:=densities.2.2.2.2.2.2.2.2
  have hcbase:=hevent V U Γ Color W Z hn0 hU G π hshort f g ρ
    (fun i x=>(marked_vortex_permutation_compatibility Q π hπ i).1 x)
    L hLsize hW hZ hstep hzlo hzhi hmin
    p kval hp.le hk.le hphys hpmin hkmin q hq hQ s hs hS a j s₀ (s₀/c) hq0 hs0 hslo htlo hmass
  let μ:=rawMarkedRetentionLaw π d hd a p kval hp.le hk.le hphys q hq hQ s hs hS
  let E:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a=>∀ i≤L,
    MarkedCommonConfigurationsWithSpokes r (G.comap (f i)) (ρ i) d βCommon ζ
      (rawMarkedRestrictPair (f i) (g i) z.1)
      (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u))
  have hbase:1-χ-(Fintype.card V:ℝ)^(-Qexp)≤μ.probability E:=by exact hcbase
  have hjoin:=finiteLaw_good_intersection μ E Extra extraErr hExtra
  change 1-χ-(Fintype.card V:ℝ)^(-Qexp)-extraErr≤μ.probability (fun z=>E z ∧ Extra z)
  linarith only [hbase,hjoin]
end Oberwolfach
