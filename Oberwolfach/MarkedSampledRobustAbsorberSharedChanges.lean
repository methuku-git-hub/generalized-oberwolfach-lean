module

public import Oberwolfach.MarkedRobustAbsorberAfterSharedChanges
public import Oberwolfach.MarkedRobustAbsorberSharedChangeMargins
public import Oberwolfach.CommonCompletionRealization
public import Oberwolfach.MarkedRetainedExtensionEvent
public import Oberwolfach.RetainedMarkedSpokeGeometry
public import Oberwolfach.MarkedReservedTerminalAbsorberProperty

@[expose] public section

/-! The original marked retention event supplies a fixed terminal absorber
for every later permitted terminal host and bounded forbidden set. The
finite family of possible remainders is counted before any of its absorbers
are chosen. No additional random sample or independence claim is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sampled_reserved_absorbers_after_shared_changes
    (k₀ l Q:ℕ) (hl:2≤l) (hlen:l+4+1=(k₀+2)*2)
    (α₀ ρstar sstar ω:ℝ) (hα₀:0<α₀) (hρstar:0<ρstar) (hsstar:0<sstar) (hω:0<ω)
    (hmargin:successorCycleRatio k₀+α₀/2≤1/2+α₀):
    ∃ ε ζ δ cap:ℝ,0<ε∧0<ζ∧0<δ∧0<cap∧∀ size:ℕ,∃ a₀ b₀ e₀:ℕ,∀ f d:ℕ,∀ hd:2≤d,∃ N:ℕ,1≤N∧
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    N≤Fintype.card V→ω*Fintype.card V≤(Fintype.card U:ℝ)→Fintype.card U≤Fintype.card V→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V),(∀ x r, 0 < r → r < 2*d+1 → (π^r) x ≠ x)→
    ∀ D:ℝ,(Fintype.card V:ℝ)/2≤D→D≤2*Fintype.card V→
      (∀ v,|(P.degree v:ℝ)-D|≤δ*Fintype.card V)→
      (∀ v,(1/2+α₀)*Fintype.card V≤(P.degree v:ℝ))→
    ∀ (ρ s₀:ℝ) (hρlo:ρstar≤ρ) (hρhi:ρ≤1) (hslo:sstar≤s₀) (hshi:s₀≤1/100),
    let densities:=marked_seed_density_bounds (l+4) (by omega) ρ s₀ ρstar sstar hρstar hsstar hρlo hρhi hslo hshi
    let p:=ρ*s₀/2
    let k:=p/((l+4:ℕ):ℝ)
    ∀ (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (g:Γ) (j:Color),
    (∀ u,q u g=s₀/((l+4:ℕ):ℝ))→(∀ u,s u j=s₀)→
    1-2/(Fintype.card V:ℝ)^Q≤
      (rawMarkedRetentionLaw π d hd g p k (densities.1.trans_le densities.2.1).le
        (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability
        (fun z=>let H:Bool→V→U→Prop := retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j
          ∀ (new:RawMarkedOutcome V U Γ Color) (Hnew:Bool→V→U→Prop)
            (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)),
            (∀ a,¬(rawMarkedPairRims P π d z.1 a↔rawMarkedPairRims P π d new a)→markedPairPhysical π a∈FR.edgeFinset)→
            (∀ b v u,¬(H b v u↔Hnew b v u)→FS.Adj (Sum.inl v) (Sum.inr u))→
            (∀ x,(FR.degree x:ℝ)≤cap*Fintype.card V)→
            (∀ x,(FS.degree x:ℝ)≤cap*Fintype.card V)→
            (∀ v u,¬(Hnew false v u∧Hnew true v u))→
          ∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
            (∀ x,(DR.degree x:ℝ)≤ζ*Fintype.card V) →
            (∀ x,(DS.degree x:ℝ)≤ζ*Fintype.card V) →
          let σ':=rawMarkedDeleteRims new DR.edgeFinset
          let H':=markedDeletePhysicalSpokes Hnew DS
          MarkedReservedTerminalAbsorberProperty
            (fun e:MarkedSampleArc P π (3*d) (fun a=>σ' (Sum.inl a)) false=>e.val.1) (fun e=>e.val.2)
            (fun e:MarkedSampleArc P π (3*d) (fun a=>σ' (Sum.inl a)) true=>e.val.1) (fun e=>e.val.2)
            (H' false) (H' true) π (3*d) l size a₀ b₀ e₀ f ε) := by
  let pstar:=min (ρstar*sstar/(2*((l+4:ℕ):ℝ))) (sstar*sstar/((l+4:ℕ):ℝ))
  let pmin:=min pstar (1/2)
  let γ:=min α₀ (1/2)
  let pret:=ω*sstar/(2*((l+4:ℕ):ℝ))
  have hpstar:0<pstar:=by dsimp [pstar];positivity
  have hpmin:0<pmin:=lt_min hpstar (by norm_num)
  have hpmin1:pmin≤1:=(min_le_right _ _).trans (by norm_num)
  have hγ:0<γ:=lt_min hα₀ (by norm_num)
  have hγ1:γ≤1:=(min_le_right _ _).trans (by norm_num)
  have hpret:0<pret:=by dsimp [pret];positivity
  have hγmargin:1/2+γ/2≤1/2+α₀:=by have hh:γ≤α₀:=min_le_left _ _;linarith
  obtain ⟨bc,bp,hbc,hbp,hcommon⟩:=marked_common_completion_realization k₀ l (by omega) hlen
    α₀ ρstar sstar ω (Q+1) hα₀ hρstar hsstar hω hmargin
  obtain ⟨hlo,hhi⟩:=successorWeightConstants_pos k₀ (α₀/2) (by positivity)
  obtain ⟨ε,ζ,hε,hζ,hδabs⟩:=marked_robust_absorber_after_shared_changes l hl
    (pmin^4*γ/8) (pmin^(l+11)*ω/4) ((sstar/((l+4:ℕ):ℝ))^2) (bc/2) (bp/2)
    (successorWeightLower k₀ (α₀/2)/2) (2*successorWeightUpper k₀ (α₀/2)/pstar^(2*(l+4)+1))
    (successorWeightUpper k₀ (α₀/2)) pstar
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) hhi hpstar
  let Kchange:=20*((l+4:ℕ)+1:ℝ)^4*(2*successorWeightUpper k₀ (α₀/2)/pstar^(2*(l+4)+1))
  have hKchange:0≤Kchange:=by dsimp [Kchange];positivity
  obtain ⟨cap,hcap,hmarginCap⟩:=marked_robust_absorber_shared_change_margins l ε Kchange (bc/2) (bp/2)
    (pmin^4*γ/8) (pmin^(l+11)*ω/4) hε hKchange (by positivity) (by positivity) (by positivity) (by positivity)
  obtain ⟨δ,hδ,hcommon⟩:=hcommon (ε/4) (by positivity)
  refine ⟨ε,ζ,δ,cap,hε,hζ,hδ,hcap,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,hδabs⟩:=hδabs size
  refine ⟨a₀,b₀,e₀,?_⟩
  intro f d hd
  obtain ⟨Na,hNa,hδabs⟩:=hδabs f d hd
  obtain ⟨Nc,hNc,hcommon⟩:=hcommon d hd
  obtain ⟨Ne,hNe,hext⟩:=marked_retained_extension_event l d (Q+1) hd ω γ pmin pret hω hγ hγ1 hpmin hpmin1 hpret
  refine ⟨max 3 (max Na (max Nc Ne)),by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ hn hUlo hUhi P π hπ D hDlo hDhi hnear hmin
  obtain ⟨weight,hw,hcommon⟩:=hcommon V U Γ Color (by omega) hUlo hUhi P π hπ D hDlo hDhi hnear hmin
  intro ρ s₀ hρlo hρhi hslo hshi densities p k q hq hQ s hs hS g j hq₀ hs₀
  obtain ⟨hweights,hwitness⟩:=hcommon ρ s₀ hρlo hρhi hslo hshi q hq hQ s hs hS g j hq₀ hs₀
  obtain ⟨hps,has,hpp,hpk,hpsbar,hsbar1,hqa,hsa,hp,hk,hphys⟩:=
    marked_common_density_bounds (l+4) (by omega) ρ s₀ ρstar sstar hρstar hsstar hρlo hρhi hslo hshi
  have hcount:=hext V U Γ Color (by omega) hUhi hUlo P π hπ
    (fun v=>(mul_le_mul_of_nonneg_right hγmargin (Nat.cast_nonneg _)).trans (hmin v))
    p k (densities.1.trans_le densities.2.1).le (densities.1.trans_le densities.2.2.1).le
    densities.2.2.2.2.2.2.2.2 ((min_le_left _ _).trans ((min_le_left _ _).trans densities.2.1))
    ((min_le_left _ _).trans ((min_le_left _ _).trans densities.2.2.1))
    q hq hQ s hs hS g j (s₀/((l+4:ℕ):ℝ)) hq₀
    (marked_common_start_mass (l+4) (by omega) ω sstar s₀ (Fintype.card V) (Fintype.card U)
      hω hsstar hslo (Nat.cast_nonneg _) hUlo)
    (by
      intro u;rw [hq₀]
      have hstar1:sstar≤1:=hslo.trans (hshi.trans (by norm_num))
      have hsquare:sstar*sstar≤s₀:=by nlinarith only [mul_nonneg hsstar.le (sub_nonneg.mpr hstar1),hslo]
      exact (min_le_left _ _).trans ((min_le_right _ _).trans
        (div_le_div_of_nonneg_right hsquare (by positivity))))
    (by intro u;rw [hs₀];exact (min_le_left _ _).trans ((min_le_left _ _).trans densities.2.2.2.1))
  let μ:=rawMarkedRetentionLaw π d hd g p k (densities.1.trans_le densities.2.1).le
    (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS
  have hjoint:=(sub_le_sub_right hcount (2/(Fintype.card V:ℝ)^(Q+1))).trans
    (finiteLaw_good_intersection μ _ _ (2/(Fintype.card V:ℝ)^(Q+1)) hwitness)
  have hn3:3≤Fintype.card V:=by omega
  have hnum:=scaled_inverse_power_le (Fintype.card V) Q (by omega) 3 (by exact_mod_cast hn3)
  have hnum':(1/(Fintype.card V:ℝ)^(Q+1))+(2/(Fintype.card V:ℝ)^(Q+1))≤1/(Fintype.card V:ℝ)^Q:=by
    convert hnum using 1 <;> ring
  have hdouble:1/(Fintype.card V:ℝ)^Q≤2/(Fintype.card V:ℝ)^Q:=
    div_le_div_of_nonneg_right (by norm_num) (by positivity)
  apply (show 1-2/(Fintype.card V:ℝ)^Q≤μ.probability _ by linarith only [hjoint,hnum',hdouble]).trans
  apply finiteLaw_probability_mono
  intro z hz
  let H:Bool→V→U→Prop:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j
  have htypes:∀ v u,¬(H false v u∧H true v u):=by
    intro v u hh
    exact retainedMarkedSpokes_disjoint π d (fun e=>z.1 (Sum.inr e)) g
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j v u hh
  have hq0:((sstar/((l+4:ℕ):ℝ))^2)≤(s₀/((l+4:ℕ):ℝ))^2:=
    pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hslo (by positivity)) 2
  intro Hout new Hnew FR FS hR hS hFR hFS htypesNew DR DS hrim hsp σ' H'
  have hnpos:(0:ℝ)<Fintype.card V:=by exact_mod_cast (show 0<Fintype.card V by omega)
  have hn0:(Fintype.card V:ℝ)≠0:=ne_of_gt hnpos
  obtain ⟨hm1,hm2,hm3,hm4,hm5,hm6,hm7⟩:=hmarginCap cap hcap.le le_rfl
  have he:(cap*Fintype.card V)/(Fintype.card V)=cap:=by field_simp
  have hcountR:(pmin^4*γ/8)*Fintype.card V≤(pmin^4*γ/4)*Fintype.card V-4*(cap*Fintype.card V):=by
    have hh:=mul_nonneg (sub_nonneg.mpr hm6) hnpos.le
    nlinarith only [hh]
  have hcountS:(pmin^(l+11)*ω/4)*Fintype.card V≤(pmin^(l+11)*ω/2)*Fintype.card V-(l+11)*(cap*Fintype.card V):=by
    push_cast at hm7
    have hh:=mul_nonneg (sub_nonneg.mpr hm7) hnpos.le
    nlinarith only [hh]
  obtain ⟨κ,hκ,hafter⟩:=hδabs V U Γ Color (by omega) P π D ((ε/4)/4)
    (successorWeightLower k₀ (α₀/2)) p k s₀ hDlo hDhi hpp hpk hpsbar
    (densities.2.2.2.2.1) (densities.2.2.2.2.2.1) hsbar1 hq0 weight hw hweights
    z.1 new H Hnew (ε/4) (ε/4) (ε/4) bc bp (pmin^4*γ/4*Fintype.card V)
    (pmin^(l+11)*ω/2*Fintype.card V) (cap*Fintype.card V) (by positivity) FR FS hR hS hFR hFS htypesNew
    (by rw [show 2*(cap*Fintype.card V)/Fintype.card V=2*cap by field_simp];linarith)
    (by rw [show 4*(cap*Fintype.card V)/Fintype.card V=4*cap by field_simp];linarith)
    (by rw [show Kchange*(cap*Fintype.card V)/Fintype.card V=Kchange*cap by field_simp];linarith)
    (by rw [show 3*(l+5:ℕ)*(cap*Fintype.card V)/Fintype.card V=3*(l+5:ℕ)*cap by field_simp];linarith)
    (by rw [show 4*(l+5:ℕ)*(cap*Fintype.card V)/Fintype.card V=4*(l+5:ℕ)*cap by field_simp];linarith)
    hcountR hcountS hz.2 hz.1
  exact hafter DR DS hrim hsp

end Oberwolfach
