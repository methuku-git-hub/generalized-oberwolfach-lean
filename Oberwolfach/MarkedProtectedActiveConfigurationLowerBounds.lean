module

public import Oberwolfach.MarkedProtectedActiveConfigurations
public import Oberwolfach.MarkedCompatibleHubRestriction
public import Oberwolfach.MarkedCommonConfigurationSpokeChanges
public import Oberwolfach.MarkedPathRestrictionCounts
public import Oberwolfach.MarkedActiveConfigurationMargins

@[expose] public section

/-! The reference configuration inequalities supply the three configuration
hypotheses for cover-down on the actual active host. Earlier spoke changes,
removed vertices, and later physical deletions have separate costs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_protected_active_configuration_lower_bounds
    (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d r:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)) (β ζ δ:ℝ)
    (hβ:0≤β) (hζ:0≤ζ) (hδ:0≤δ)
    (hDR:∀ x,((DR.comap f).degree x:ℝ)≤δ)
    (hDSrow:∀ x,((DS.comap (Sum.map f g)).degree (Sum.inl x):ℝ)≤δ)
    (hDScol:∀ u,((DS.comap (Sum.map f g)).degree (Sum.inr u):ℝ)≤δ)
    (hparent:MarkedCommonConfigurationsWithSpokes r P π d β ζ σ H)
    (hrows:2*(r+5:ℝ)*((Finset.univ\Finset.univ.image f).card+ζ*Fintype.card V)+
      4*(r+5:ℝ)*δ≤12*β*Fintype.card V)
    (hhubs:(Finset.univ\Finset.univ.image g).card+(r+5:ℝ)*(δ+ζ*Fintype.card V)≤28*β*Fintype.card V):
    let σA:=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset)
    let HA:=fun b x u=>markedDeletePhysicalSpokes H DS b (f x) (g u)
    let EA:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) false
    let KA:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) true;
    (∀ C:MarkedCycleTuple (fun e:EA=>e.val.1) (fun e=>e.val.2) (fun e:KA=>e.val.1) (fun e=>e.val.2)
      (r+4) ρ (3*d),4*β*Fintype.card W≤(Fintype.card {u // MarkedHubCompatible (HA false) (HA true) C.val u}:ℝ))∧
    (∀ u u':Z,u≠u'→4*β*(Fintype.card W:ℝ)^(r+5)≤
      (Fintype.card (CommonMarkedCycle (fun e:EA=>e.val.1) (fun e=>e.val.2) (fun e:KA=>e.val.1) (fun e=>e.val.2)
        (r+4) ρ (3*d) (HA false) (HA true) u u'):ℝ))∧
    (∀ j (x x':W) (u u':Z),x≠x'→u≠u'→4*β*(Fintype.card W:ℝ)^(r+4)≤
      (Fintype.card (CanonicalCommonMarkedPath (fun e:EA=>e.val.1) (fun e=>e.val.2)
        (fun e:KA=>e.val.1) (fun e=>e.val.2) (r+4) ρ (3*d) (HA false) (HA true)
        ((markedRootOrder (r+4) j).symm 0) x x' u u'):ℝ)):=by
  intro σA HA EA KA
  have hn:(Fintype.card W:ℝ)≤Fintype.card V:=Nat.cast_le.mpr (Fintype.card_le_of_injective f f.injective)
  have hpow (k:ℕ):(Fintype.card W:ℝ)^k≤(Fintype.card V:ℝ)^k:=pow_le_pow_left₀ (by positivity) hn k
  obtain ⟨hcycle,hpath⟩:=marked_protected_active_common_configurations f g π ρ hf P d (r+4) (by omega)
    σ H DR DS δ hDR hDScol
  dsimp only at hcycle hpath
  constructor
  · intro C
    have hs:PermutationSeparated π (3*d) (f∘C.val):=
      (permutationSeparated_embedding_iff f.toEmbedding ρ π hf (3*d) C.val).mpr C.property.1
    have hp:=hparent.1 (f∘C.val) hs
    have hl:=marked_protected_active_compatible_hubs f.toEmbedding g H DS δ hDSrow C.val
    have hcompat:(potentialMarkedHubs HA C.val).card=Fintype.card {u // MarkedHubCompatible (HA false) (HA true) C.val u}:=by
      rw [Fintype.card_subtype]
      congr 1
      ext u
      simp only [potentialMarkedHubs,common,Finset.mem_filter,Finset.mem_univ,true_and]
      rw [markedHubCompatible_iff_positions]
      simp only [true_implies,markedPositionType]
      apply forall_congr'
      intro i
      by_cases hi:i=0 <;> simp [hi]
    have hl':((potentialMarkedHubs H (f∘C.val)).card:ℝ)-(potentialMarkedHubs HA C.val).card≤
        (Finset.univ\Finset.univ.image g).card+(r+5:ℕ)*δ:=by
      convert hl using 1 <;> congr! <;> omega
    clear hl
    have hl:=hl'
    rw [hcompat] at hl
    have hn':=mul_le_mul_of_nonneg_left hn (by positivity:0≤4*β)
    push_cast at hp hl hhubs
    nlinarith only [hp,hl,hhubs,hn']
  constructor
  · intro u u' huu
    let us:Fin 2→U:=![g u,g u']
    have hi:Function.Injective us:=by
      intro i j he
      fin_cases i <;> fin_cases j <;> simp_all [us,g.injective.eq_iff]
    have hp:=hparent.2.1 us hi
    have hl:=hcycle u u'
    have hpw:=mul_le_mul_of_nonneg_left (hpow (r+5)) (by positivity:0≤4*β)
    have hδw:=mul_le_mul_of_nonneg_left (hpow (r+4)) (by positivity:0≤3*(r+5:ℝ)*δ)
    have hbud:=mul_le_mul_of_nonneg_right hrows (by positivity:0≤(Fintype.card V:ℝ)^(r+4))
    have hdextra:0≤(r+5:ℝ)*δ*(Fintype.card V:ℝ)^(r+4):=by positivity
    dsimp only [MarkedSampleCommonCycleWithSpokes,us,Matrix.cons_val_zero,Matrix.cons_val_one] at hp
    simp only [Fintype.card_eq_nat_card] at hp hl ⊢
    push_cast at hp hl
    simp only [show r+5=(r+4)+1 by omega,pow_succ] at hp hpw ⊢
    dsimp only [EA,KA,σA,HA]
    simp only [Fintype.card_eq_nat_card,pow_succ] at hp hl hpw hδw hbud hdextra ⊢
    nlinarith only [hp,hl,hpw,hδw,hbud,hdextra]
  · intro j x x' u u' hxx huu
    let us:Fin 2→U:=![g u,g u']
    have hi:Function.Injective us:=by
      intro i j he
      fin_cases i <;> fin_cases j <;> simp_all [us,g.injective.eq_iff]
    have hp:=hparent.2.2 (f x) (f x') (fun he=>hxx (f.injective he)) us hi j
    have he:=Fintype.card_congr (rootFirstCommonMarkedPathCanonicalEquiv
      (tail:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1)
      (head:=fun e=>e.val.2) (ktail:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1)
      (khead:=fun e=>e.val.2) (m:=r+4) (π:=π) (b:=3*d) (H₀:=H false) (Hₖ:=H true)
      j (f x) (f x') (g u) (g u'))
    dsimp only [MarkedSampleCommonPathWithSpokes,us,Matrix.cons_val_zero,Matrix.cons_val_one] at hp
    simp only [show r+3+1=r+4 by omega,Fintype.card_eq_nat_card] at hp he
    rw [he] at hp
    have hl:=hpath ((markedRootOrder (r+4) j).symm 0) x x' u u'
    have hpw:=mul_le_mul_of_nonneg_left (hpow (r+4)) (by positivity:0≤4*β)
    have hδw:=mul_le_mul_of_nonneg_left (hpow (r+3)) (by positivity:0≤4*(r+5:ℝ)*δ)
    have hbud:=mul_le_mul_of_nonneg_right hrows (by positivity:0≤(Fintype.card V:ℝ)^(r+3))
    have hextra:0≤2*((Finset.univ\Finset.univ.image f).card+ζ*Fintype.card V)*(Fintype.card V:ℝ)^(r+3):=by positivity
    simp only [show r+4-1=r+3 by omega,Fintype.card_eq_nat_card] at hl ⊢
    push_cast at hp hl
    simp only [show r+4=(r+3)+1 by omega,pow_succ] at hp hpw ⊢
    dsimp only [EA,KA,σA,HA]
    simp only [Fintype.card_eq_nat_card,pow_succ] at hp hl hpw hδw hbud hextra ⊢
    nlinarith only [hp,hl,hpw,hδw,hbud,hextra]

end Oberwolfach
