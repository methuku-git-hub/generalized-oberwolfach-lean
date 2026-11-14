module

public import Oberwolfach.MarkedRetainedRowsVortex
public import Oberwolfach.MarkedVortexNonDeeperHubEmbedding
public import Oberwolfach.MarkedParentHubsNextActiveSize
public import Oberwolfach.MarkedRetainedLocalLoadVortex
public import Oberwolfach.MarkedVortexActiveGeometryBounds
public import Oberwolfach.MarkedVortexActiveDegreeFields
public import Oberwolfach.MarkedNestedVortexActiveGeometry
public import Oberwolfach.MarkedRetainedConfigurationsVortex
public import Oberwolfach.MarkedFixedVortexParentDegrees
public import Oberwolfach.MarkedSeedDensities
public import Oberwolfach.MarkedActiveSizeThreshold
public import Oberwolfach.MarkedActiveSeedMass
public import Oberwolfach.VortexSamplingDomainSizes

@[expose] public section
/-! Retained local configuration estimates on the actual fixed parent vortex levels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_actual_next_active_nondeeper_hubs_rows_event_uniform_failure
    (r c:ℕ) (hr:1≤r) (hc:3≤c) (α ρ₀ sstar tstar kstar Qexp rowErr:ℝ)
    (hα:0<α) (hα1:α≤1) (hρ₀:0<ρ₀) (hsstar:0<sstar) (htstar:0<tstar) (htstar1:tstar≤1)
    (hkstar:0<kstar) (hrowErr:0<rowErr):
    ∃ βmax:ℝ,0<βmax ∧ ∀ χ:ℝ,0<χ→∀ (d:ℕ) (hd:2≤d),∀ ε:ℝ,0<ε→ε≤1/4→∀ ζ:ℝ,0<ζ→∃ N₀ m₀:ℕ,1≤N₀ ∧ 1≤m₀ ∧
    ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),
    G.IsRegularOfDegree D→∀ (hn:0<Fintype.card V),N₀≤Fintype.card V→
    (1/2+α)*Fintype.card V≤(D:ℝ)→∀ (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1),
    0≤β→β≤βmax→m₀≤m→∀ (π:Equiv.Perm V)
      (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
    (∀ x l,0<l→l<2*d+1→(π^l) x≠x)→∀ L:ℕ,L<Q.length→
    letI : Nonempty V:=Fintype.card_pos_iff.mp hn
    let A:=fun i=>Finset.univ\markedVortexInnerVertices Q i
    let B:=fun i=>Finset.univ\markedVortexInnerHubs Q i
    let W:=fun i=>↥(A (i+1))
    let Z:=markedVortexNonDeeperHubType Q
    let f:=fun i=>markedVortexActiveVertexEmbedding Q (i+1)
    let g:=markedVortexNonDeeperHubToPhysical Q
    let ρ:=fun i=>markedVortexActivePermutation Q π hπ (i+1);
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
      (fun z=>(∀ i≤L,MarkedRowsWithSpokes (G.comap (f i)) (ρ i) d 1 Finset.univ p kval
        (fun u=>q (g i u)) (fun u=>s (g i u)) a j ((rowErr+ζ)*Fintype.card (W i))
        (rawMarkedRestrictPair (f i) (g i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u))) ∧ Extra z):=by
  let βmax:=min (3*α/40) (3/20)
  have hβmax:0<βmax:=by dsimp [βmax];positivity
  refine ⟨βmax,hβmax,?_⟩
  intro χ hχ d hd
  let pstar:=ρ₀*tstar/4
  have hpstar:0<pstar:=by dsimp [pstar];positivity
  intro ε he he1 ζ hζ
  let K:ℝ:=4/ε
  have hK:1≤K:=by dsimp [K];apply (le_div_iff₀ he).2;linarith
  obtain ⟨M₀,N₀,hM₀,hN₀,hevent⟩:=marked_retained_rows_vortex_event 1 d hd rowErr K (1/2) χ 1 Qexp pstar ζ
    hrowErr hK (by norm_num) (by norm_num) hχ hpstar hζ
  obtain ⟨m₀,hm₀,hsize⟩:=marked_active_size_threshold ρ₀ ε hρ₀ he M₀ M₀
  refine ⟨N₀,m₀,hN₀,hm₀,?_⟩
  intro V U _ _ _ _ G D m β Q hreg hn hn0 hD hρlo hρhi hb hbmax hm π hπ hshort L hL A B W Z f g ρ
  letI : Nonempty V:=Fintype.card_pos_iff.mp hn
  have hρ:0< initialIndexDensity U D:=hρ₀.trans_le hρlo
  have hbα:β≤3*α/40:=hbmax.trans (min_le_left _ _)
  have hb1:β≤3/20:=hbmax.trans (min_le_right _ _)
  obtain ⟨hsizeW,hsizeA,hsizeB⟩:=hsize m hm
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
  have hbgeom:β≤1/4:=by linarith
  have hgeom (i:ℕ) (hi:i≤Q.length):=marked_nested_vortex_active_geometry Q ρ₀ hρ₀ hreg hn hDhalf hρlo hρhi hb hbgeom he.le he1 i hi
  have hW (i:ℕ) (hi:i≤L):M₀≤Fintype.card (W i):=by
    have hh:=hsizeA.trans (hgeom (i+1) (by omega)).2.2.2.1
    change M₀≤Fintype.card ↥(A (i+1))
    rw [Fintype.card_coe]
    exact_mod_cast hh
  have hZ (i:ℕ) (hi:i≤L):M₀≤Fintype.card (Z i):=by
    have hh:=hsizeB.trans (hgeom i (by omega)).2.2.2.2
    have hsub:(B i)⊆(Finset.univ\markedVortexDeeperHubs Q i):=by
      intro u hu
      have hnot:u∉markedVortexInnerHubs Q i:=(Finset.mem_sdiff.mp hu).2
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro hd
      apply hnot
      simp only [markedVortexInnerHubs,markedVortexDeeperHubs,Finset.mem_filter,Finset.mem_univ,true_and] at hd ⊢
      exact (Q.extendedIndices_subset (Nat.add_le_add_left (Nat.le_succ 1) i)) hd
    have hcard: (B i).card≤(Finset.univ\markedVortexDeeperHubs Q i).card:=Finset.card_le_card hsub
    change M₀≤Fintype.card ↥((Finset.univ\markedVortexDeeperHubs Q i):Finset (markedVortexHubType Q i))
    rw [Fintype.card_coe]
    exact_mod_cast (show (M₀:ℝ)≤(Finset.univ\markedVortexDeeperHubs Q i).card by exact hh.trans (by exact_mod_cast hcard))
  have hstep (i:ℕ) (hi:i<L):(Fintype.card (W (i+1)):ℝ)≤(1/2)*Fintype.card (W i):=by
    have hh:(((A (i+2)).card):ℝ)≤(4*ε/3)*(A (i+1)).card:=by simpa only [Nat.add_assoc] using (hgeom (i+1) (by omega)).2.2.1
    have ha:(0:ℝ)≤(A (i+1)).card:=Nat.cast_nonneg _
    change ((Fintype.card ↥(A (i+2))):ℝ)≤(1/2)*Fintype.card ↥(A (i+1))
    rw [Fintype.card_coe,Fintype.card_coe]
    nlinarith
  have hzhi (i:ℕ) (hi:i≤L):(Fintype.card (Z i):ℝ)≤K*Fintype.card (W i):=by
    have hparent:=marked_parent_hubs_next_active_size Q ρ₀ hρ₀ hreg hn hDhalf hDpos hρlo hρhi hb hbgeom he he1 hmpos i (by omega)
    have hsub:(Fintype.card (Z i):ℝ)≤Fintype.card (markedVortexHubType Q i):=by
      change (Fintype.card ↥((Finset.univ\markedVortexDeeperHubs Q i):Finset (markedVortexHubType Q i)):ℝ)≤_
      rw [Fintype.card_coe]
      exact_mod_cast (Finset.card_le_univ (Finset.univ\markedVortexDeeperHubs Q i))
    exact hsub.trans hparent
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
  have hA (i:ℕ) (hi:i≤L):M₀≤(Finset.univ:Finset (W i)).card:=by simpa using hW i hi
  have hWsize (i:ℕ) (hi:i≤L):(Fintype.card (W i):ℝ)≤K*((Finset.univ:Finset (W i)).card):=by
    simp only [Finset.card_univ]
    nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card (W i))]
  have hZsize (i:ℕ) (hi:i≤L):(Fintype.card (Z i):ℝ)≤K*((Finset.univ:Finset (W i)).card):=by
    simpa only [Finset.card_univ] using hzhi i hi
  have hAstep (i:ℕ) (hi:i<L):(((Finset.univ:Finset (W (i+1))).card:ℝ))≤(1/2)*(Finset.univ:Finset (W i)).card:=by simpa using hstep i hi
  have hcbase:=hevent V U Γ Color W Z hn0 hU G π hshort f g ρ
    (fun i x=>marked_vortex_active_permutation_embedding Q π hπ (i+1) x)
    (fun i=>Finset.univ) L hLsize hA hZ hAstep hWsize hZsize (by intro i hi x;simp)
    p kval hp.le hk.le hphys q hq hQ s hs hS a j (s₀/c) hq0 hmass
  let μ:=rawMarkedRetentionLaw π d hd a p kval hp.le hk.le hphys q hq hQ s hs hS
  let E:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a=>∀ i≤L,
    MarkedRowsWithSpokes (G.comap (f i)) (ρ i) d 1 Finset.univ p kval
        (fun u=>q (g i u)) (fun u=>s (g i u)) a j ((rowErr+ζ)*Fintype.card (W i))
      (rawMarkedRestrictPair (f i) (g i) z.1)
      (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u))
  have hbase:1-χ-(Fintype.card V:ℝ)^(-Qexp)≤μ.probability E:=by
    dsimp only [μ,E]
    simpa only [Nat.cast_one,one_mul,Finset.card_univ] using hcbase
  have hjoin:=finiteLaw_good_intersection μ E Extra extraErr hExtra
  change 1-χ-(Fintype.card V:ℝ)^(-Qexp)-extraErr≤μ.probability (fun z=>E z ∧ Extra z)
  linarith only [hbase,hjoin]
end Oberwolfach
