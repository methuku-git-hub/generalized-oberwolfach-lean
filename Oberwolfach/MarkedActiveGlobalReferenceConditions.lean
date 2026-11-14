module

public import Oberwolfach.MarkedActiveGlobalConditions
public import Oberwolfach.MarkedActiveReferenceDegreesFromScale
public import Oberwolfach.MarkedActiveReferenceCutsFromScale
public import Oberwolfach.MarkedActiveConfigurationsFromScale
public import Oberwolfach.MarkedActiveSpokeDataFromScale
public import Oberwolfach.MarkedActiveSeedScale

@[expose] public section

/-! A single choice of reference accuracy supplies every global input of
the actual active cover-down constructor, uniformly over the later physical
deletions. Coefficients, domains and potential-root exclusions are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_active_global_reference_conditions
    (r h:ℕ) (hh:3≤h)
    (rho gamma omega t p0 beta aLo B eps eta0 delta0:ℝ)
    (hrho:0<rho) (hrho1:rho≤1) (hg:0<gamma) (ho:0<omega) (ho1:omega≤1)
    (ht:0<t) (ht1:(r+4:ℝ)*t≤1) (hp0:0<p0)
    (hpr:p0≤rho*(r+4:ℝ)*t/2) (hpk:p0≤rho*t/2) (hpt:p0≤t)
    (hb:0<beta) (ha:0<aLo) (hB:0≤B) (he:0<eps) (heta:0<eta0) (hd:0<delta0):
    ∃ kappa0:ℝ,0<kappa0∧∀ kappa:ℝ,0<kappa→kappa≤kappa0→
    ∀ d:ℕ,∃ N:ℕ,1≤N∧
    ∀ (V U A Z Γ Color:Type) [Fintype V] [Fintype U] [Fintype A] [Fintype Z]
      [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder A] [DecidableEq U] [DecidableEq Z],
    N≤Fintype.card V→Fintype.card U≤Fintype.card V→ omega*Fintype.card V≤(Fintype.card U:ℝ)→
    ∀ (f:A↪oV) (g:Z↪U) (P:SimpleGraph V) (π:Equiv.Perm V) (ρ:Equiv.Perm A),
    (∀ x,f (ρ x)=π (f x))→
    ∀ (T:Finset V) (W:Finset U),(∀ x,π x∈T↔x∈T)→
    Finset.univ.image f=Finset.univ\T→Finset.univ.image g=Finset.univ\W→
    (T.card:ℝ)≤kappa*Fintype.card V→(W.card:ℝ)≤kappa*Fintype.card V→
    (∀ x,(1/2+gamma/2)*Fintype.card V≤(P.degree x:ℝ))→
    (∀ x,|(P.degree x:ℝ)-2*Fintype.card U/rho|≤kappa*Fintype.card V)→
    ∀ (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (c:Color),
    (∀ u,q u a=t)→(∀ u,s u c=(r+4:ℝ)*t)→
    ∀ (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop),
    let p:=rho*(r+4:ℝ)*t/2
    let k:=p/(r+4:ℝ)
    let D:=2*Fintype.card U/rho;
    MarkedReferenceStatistics P π d a c D kappa kappa gamma p k ((r+4:ℝ)*t) t σ→
    MarkedReferenceCutFamilies P π d a c gamma p k t σ→
    MarkedCommonConfigurationsWithSpokes r P π d beta kappa σ H→
    MarkedRowsWithSpokes P π d h Finset.univ p k q s a c (kappa*Fintype.card V) σ H→
    MarkedIndicesWithSpokes π d h Finset.univ q s a c (kappa*Fintype.card V) σ H→
    (∀ mark x,(∑ u,if ¬(rawMarkedPairSpokes π d σ a c mark x u↔H mark x u) then (1:ℝ) else 0)≤kappa*Fintype.card U)→
    (∀ mark u,(∑ x,if ¬(rawMarkedPairSpokes π d σ a c mark x u↔H mark x u) then (1:ℝ) else 0)≤kappa*Fintype.card V)→
    (Fintype.card V:ℝ)/2≤D→D≤2*Fintype.card V→
    ∀ (tau:ℝ) (weight:(Fin (r+4+1)→V)→ℝ),SuccessorSequenceWeightConditions P π (3*d) D tau aLo B weight→
    (let seed:=fun C:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd (r+4) π (3*d)
        (fun (_:V) (_:U)=>True) (fun _ _=>True)=>weight C.1.val/(D*p^(r+4)*k*((r+4:ℝ)*t)^(r+4));
      ∀ root,rawMarkedWheelMarginal P π d p k q s a c root≠0→
        |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root-1|≤kappa)→
    ∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
    (∀ x,((DR.comap f).degree x:ℝ)≤kappa*Fintype.card V)→
    (∀ x,((DS.comap (Sum.map f g)).degree (Sum.inl x):ℝ)≤kappa*Fintype.card V)→
    (∀ u,((DS.comap (Sum.map f g)).degree (Sum.inr u):ℝ)≤kappa*Fintype.card V)→
    let σA:=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset)
    let HA:=fun b x u=>markedDeletePhysicalSpokes H DS b (f x) (g u)
    let EA:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) false
    let KA:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) true;
    MarkedActiveGlobalConditions (fun e:EA=>e.val.1) (fun e=>e.val.2)
      (fun e:KA=>e.val.1) (fun e=>e.val.2) ρ d r (HA false) (HA true)
      p (2*Fintype.card Z/rho) (gamma/8) beta (max 1 (1/p0)) ((aLo/2)/2^(r+4))
      (2*B/p0^(2*(r+4)+1)) (omega/2) eps eta0 delta0
      ((min (min gamma p0) t/256)/2) (min (gamma*p0) t/128):=by
  let C:=2*B/p0^(2*(r+4)+1)
  let delta:=min (min gamma p0) t/256
  let hcut:=min (gamma*p0) t/128
  have hC:0≤C:=by dsimp [C];positivity
  have hdelta:0<delta:=by dsimp [delta];positivity
  have hhcut:0<hcut:=by dsimp [hcut];positivity
  obtain ⟨kappa0,hkappa0,hscale⟩:=marked_active_reference_scale_exists r h omega gamma p0 beta eps
    (delta0/2) eta0 C rho delta hcut ho hg hp0 hb he (by positivity) heta hC hrho hdelta hhcut
  refine ⟨kappa0,hkappa0,?_⟩
  intro kappa hkappa hkk d
  obtain ⟨N,hN,horder⟩:=marked_active_exception_order omega delta0 ho hd d
  refine ⟨N,hN,?_⟩
  intro V U A Z Γ Color _ _ _ _ _ _ _ _ _ _ hn hu hubs f g P π ρ hf T W hT hfX hgX hTsize hWsize
    hdeg hreg q s a c hq hs σ H p k D hstats hcuts hconfigs hrows hindices hrowOld hcolOld hDlo hDhi
    tau weight hw hload DR DS hrim hrow hcol σA HA EA KA
  obtain ⟨hc0,hc1,hc2,hc3,hc4,hc5,hc6,hc7,hc8,hc9,hc10,hc11,hc12,hc13,hc14⟩:=hscale kappa hkappa.le hkk
  have hn':0<Fintype.card V:=lt_of_lt_of_le (by omega) hn
  have hn0:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn'
  have hTr:Finset.univ\Finset.univ.image f=T:=by rw [hfX];simp
  have hWr:Finset.univ\Finset.univ.image g=W:=by rw [hgX];simp
  have hTsize':((Finset.univ\Finset.univ.image f).card:ℝ)≤kappa*Fintype.card V:=hTr.symm ▸ hTsize
  have hWsize':((Finset.univ\Finset.univ.image g).card:ℝ)≤kappa*Fintype.card V:=hWr.symm ▸ hWsize
  have hRf:(Fintype.card V:ℝ)-Fintype.card A≤kappa*Fintype.card V:=by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
      Finset.card_image_of_injective _ f.injective,Finset.card_univ,
      Nat.cast_sub (Fintype.card_le_of_injective f f.injective)] at hTsize'
    exact hTsize'
  have hUg:(Fintype.card U:ℝ)-Fintype.card Z≤kappa*Fintype.card V:=by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
      Finset.card_image_of_injective _ g.injective,Finset.card_univ,
      Nat.cast_sub (Fintype.card_le_of_injective g g.injective)] at hWsize'
    exact hWsize'
  obtain ⟨hA34,hAhalf,hZhalf,hApos,hZpos,hAr,hZr,hAR,hZR⟩:=marked_active_reference_geometry_from_scale
    (Fintype.card V) (Fintype.card U) (Fintype.card A) (Fintype.card Z) omega kappa delta
    hn0 ho ho1 hkappa.le hc11 hc13 hdelta.le hc9 hRf hUg hubs
  have hp:0≤p:=by dsimp [p];positivity
  have ht1':t≤1:=by have hr:0≤(r:ℝ):=Nat.cast_nonneg r;nlinarith only [ht1,mul_nonneg hr ht.le,ht.le]
  have hp1:p≤1/2:=by
    have hh:=mul_le_mul_of_nonneg_left ht1 hrho.le
    dsimp [p]
    nlinarith only [hh,hrho1]
  have hkform:k=rho*t/2:=by dsimp [k,p];field_simp <;> ring
  have hpk':p0≤k:=by rw [hkform];exact hpk
  have hk0:0≤k:=hp0.le.trans hpk'
  have hk1:k≤1:=by
    have hr:1≤(r+4:ℝ):=by have hh:=Nat.cast_nonneg (α:=ℝ) r;linarith
    exact (div_le_self hp hr).trans (by linarith : p≤1)
  have hs0:p0≤(r+4:ℝ)*t:=by
    have hr:0≤(r:ℝ):=Nat.cast_nonneg r
    nlinarith only [hpt,mul_nonneg hr ht.le,ht.le]
  have htw:3*kappa≤gamma*p^2:=hc1.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp0.le hpr 2) hg.le)
  obtain ⟨hDAl,hDAu,hZlo,hZhi,hdegrees,htwosteps⟩:=marked_active_reference_degrees_from_scale
    f g P π ρ hf d r hn' rho gamma omega t kappa eps kappa ((r+4:ℝ)*t) t
    hrho hrho1 hg ho ho1 ht.le ht1 hkappa.le hc11 hc14 hc12 hc13 hc0 htw
    hdeg hreg hubs hTsize' hWsize' σ DR a c hstats hrim
  have hOrd:kappa≤min ((gamma/8)/16) (p/128):=by
    apply hc7.trans
    apply min_le_min
    · exact le_of_eq (by ring)
    · exact div_le_div_of_nonneg_right hpr (by norm_num)
  have hOrdLoss:2*kappa≤gamma*p/8:=hc8.trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpr hg.le) (by norm_num))
  obtain ⟨hOrdCut,hRcuts,hScuts⟩:=marked_active_reference_cuts_from_scale
    f g π ρ hf P d hn' σ H a c gamma omega p0 t p k kappa
    hg ho ho1 hp0 ht hpr hpk' (by linarith only [hp1]) ht1' hkappa.le hc11 hc13 hubs hRf hUg
    hOrd hOrdLoss hc9 hc10 hcuts hrowOld hcolOld DR DS hrim hrow hcol
  obtain ⟨hHub,hCycles,hPaths⟩:=marked_active_configurations_from_scale f g π ρ hf P d r σ H DR DS
    beta kappa hb.le hkappa.le hrim hrow hcol hconfigs hTsize' hWsize' hc2 hc3
  let density:Bool→ℝ:=fun j=>if j then t else (r+4:ℝ)*t
  have hden0:∀ j,p0≤density j:=by intro j;cases j <;> simp only [density,Bool.false_eq_true,ite_false,ite_true] <;> assumption
  have hden1:∀ j,density j≤1:=by intro j;cases j <;> simp only [density,Bool.false_eq_true,ite_false,ite_true] <;> assumption
  have hden:∀ b u,(if b then q u a else s u c)=density b:=by intro b u;cases b <;> simp [density,hq,hs]
  have hdata:=marked_active_spoke_data_from_scale f g π ρ hf P d h hh p k q s a c
    ⟨hp,by linarith only [hp1]⟩ ⟨hk0,hk1⟩ (by intro u;rw [hq];exact ⟨ht.le,ht1'⟩)
    (by intro u;rw [hs];exact ⟨by positivity,ht1⟩) kappa omega p0 (delta0/2) hkappa.le ho
    hAhalf hZhalf hTsize' hWsize' hc4 hc5 density hp0 hden0 hden1 hden σ H hrows hindices DR DS hrim hrow hcol
  have hseedBudget:(1+2*((r+4:ℕ)+1:ℝ)^3*(2*B/p0^(2*(r+4)+1))+
      66*((r+4:ℕ)+1:ℝ)^4*(2*B/p0^(2*(r+4)+1)))*kappa≤eta0:=by
    simpa only [Nat.cast_add,Nat.cast_ofNat,C,show (r:ℝ)+4+1=r+5 by ring] using hc6
  obtain ⟨hRload,hSload,hweights⟩:=marked_active_seed_from_scale f g ρ P π d (r+4) (by omega) hn' hu
    D tau aLo B p k ((r+4:ℝ)*t) p0 kappa kappa eta0 hDlo hDhi hp0 hpr hpk' hs0
    (by linarith only [hp1]) hk1 ht1 ha.le hB hkappa.le le_rfl hkappa.le hseedBudget
    weight hw σ H q s a c (by intro u;rw [hq];exact ht) (by intro u;rw [hs];positivity)
    hload T W hT hf hfX hgX hAhalf hZhi hTsize hWsize DR DS hrim hrow hcol
  refine {
    degree_lower:=hDAl
    degree_upper:=hDAu
    ordinary_out:=?_
    ordinary_in:=?_
    marked_out:=?_
    marked_in:=?_
    two_step:=htwosteps
    ordinary_cut:=hOrdCut
    compatible_hubs:=hHub
    hubs_lower:=hZlo
    hubs_upper:=hZhi
    spoke_intersections:=?_
    common_cycles:=hCycles
    common_paths:=?_
    seed_weights:=?_
    ordinary_correction_cut:=hRcuts false
    marked_correction_cut:=hRcuts true
    ordinary_spoke_cut:=hScuts false
    marked_spoke_cut:=hScuts true }
  · intro x;simpa only [Bool.false_eq_true,ite_false] using (hdegrees false x).1
  · intro x;simpa only [Bool.false_eq_true,ite_false] using (hdegrees false x).2
  · intro x;simpa only [ite_true,p,div_mul_eq_mul_div] using (hdegrees true x).1
  · intro x;simpa only [ite_true,p,div_mul_eq_mul_div] using (hdegrees true x).2
  · refine ⟨fun j _=>density j,fun j _=>1/density j,delta0/2,6*d+1,?_,?_⟩
    · intro j;cases j <;> exact hdata _
    · exact horder (Fintype.card V) hn (Fintype.card A) (Fintype.card Z) (delta0/2) hAhalf hZhalf le_rfl
  · intro j Q
    exact hPaths j Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2 Q.property.1 Q.property.2.1
  · exact ⟨_,hRload,hSload,hweights⟩

end Oberwolfach
