module

public import Oberwolfach.MarkedEmbeddedFreshHubEvent
public import Oberwolfach.MarkedSampleHubCountTransfer
public import Oberwolfach.MarkedSampleHubLoadTransfer
public import Oberwolfach.MarkedSampleHubClassSizes
public import Oberwolfach.MarkedSampleCycleValidity
public import Oberwolfach.SuccessorSeedBounds

@[expose] public section

/-! Actual fixed sampled profiles and root-omitted loads supply the inner
fresh-factor event. The cycle coefficients precede this boundary sampling;
its tolerance has no dependence on the ambient/inner size ratio. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sample_fresh_inner_hub_event (r:ℕ) (β aLo B pstar t:ℝ)
    (hβ:0<β) (haLo:0<aLo) (hB:0≤B) (hpstar:0<pstar) (ht:0<t):
    ∃ η ζ:ℝ,0<η∧0<ζ∧∀ (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃ N:ℕ,1≤N∧
    ∀ (W V U Gamma Color J:Type) [Fintype W] [LinearOrder W] [Fintype V] [DecidableEq V]
      [Fintype U] [DecidableEq U] [Fintype Gamma] [Fintype Color] [Fintype J],
    N≤Fintype.card W→Fintype.card J≤(Fintype.card W)^2→
    ∀ (f:W↪V) (ρ:Equiv.Perm W) (π:Equiv.Perm V),(∀ x,f (ρ x)=π (f x))→
    ∀ (P:SimpleGraph W) (d:ℕ) (D τ pr kr sr:ℝ),
    (Fintype.card W:ℝ)/2≤D→D≤2*Fintype.card W→
    pstar≤pr→pstar≤kr→pstar≤sr→pr≤1→kr≤1→sr≤1→
    ∀ weight:(Fin (r+4+1)→W)→ℝ,SuccessorSequenceWeightConditions P ρ (3*d) D τ aLo B weight→
    ∀ (σ:RawMarkedOutcome W U Gamma Color) (H:Bool→W→U→Prop) (u:J→U),
    (∀ j v,¬(H false v (u j)∧H true v (u j)))→
    (∀ j v z,H false v (u j)→H true z (u j)→v≠ρ z)→
    ∀ (Q:U→Gamma→ℝ) (S:U→Color→ℝ) (g:Gamma) (c:Color),
    (∀ u,Q u g=t)→
    MarkedRowsWithSpokes P ρ d 1 Finset.univ pr kr Q S g c ((t/2)*Fintype.card W) σ H→
    MarkedLocalConfigurationsWithSpokes r P ρ d Finset.univ β β σ H→
    MarkedLocalSpokeLoadsWithSpokes P ρ d (r+4) D pr kr sr weight η σ H→
    let E:=MarkedSampleArc P ρ (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P ρ (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    1-1/(Fintype.card W:ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (fun σb=>∀ j (Y:Finset W),(∀ v∈Y,H false v (u j)∨H true v (u j))→
          (Y.filter (fun v=>H false v (u j))).card=(r+4)*(Y.filter (fun v=>H true v (u j))).card→
          ((changed Y ((Finset.univ.filter (fun v=>H false v (u j)∨H true v (u j))).filter
            (fun v=>σb s(Sum.inl (f v),Sum.inr (u j))=true))).card:ℝ)≤ζ*(p*Fintype.card W)→
          ∀ F:SimpleGraph V,(∀ v,(F.degree v:ℝ)≤ζ*(p*Fintype.card W))→
          ∃ R:MarkedHubFactorOn (f∘tail) (f∘head) (f∘ktail) (f∘khead) (r+4) π (3*d)
            (spokeRelationImage f (H false)) (spokeRelationImage f (H true)) (u j) (Y.image f),Disjoint R.rim F):=by
  obtain ⟨η,ζ,hη,hζ,hbase⟩:=marked_embedded_fresh_hub_common_event (r+4) (by omega) β (t/2)
    (aLo/2) (2*B/pstar^(2*(r+4)+1)) hβ (by positivity) (by positivity) (by positivity)
  refine ⟨η,ζ,hη,hζ,?_⟩
  intro p hp hp1 q
  obtain ⟨N,hN⟩:=hbase p hp hp1 q
  refine ⟨max N 1,by omega,?_⟩
  intro W V U Gamma Color J _ _ _ _ _ _ _ _ _ hn hJ f ρ π hf P d D τ pr kr sr
    hDlo hDhi hp hk hs hp1' hk1 hs1 weight hw σ H u hdis hsep Q S g c hQ hrows hconfigs hload
    E K tail head ktail khead
  have hnpos:0<Fintype.card W:=by omega
  have hcounts:=marked_local_configurations_hub_counts r P ρ d Finset.univ β β σ H hconfigs
  have hclass:=marked_sample_hub_class_lower P ρ d 1 (by omega) pr kr t (t/2) Q S g c hQ le_rfl σ H hrows
  apply hN W V U E K J (by omega) hJ f ρ π hf tail head ktail khead (3*d) (H false) (H true) u
    hdis (markedSampleArc_physical_injective P ρ (3*d) _) hsep _ _ _
    (fun _ C=>weight C.val/(D*pr^(r+4)*kr*sr^(r+4))) _ _
  · intro j
    have hh:(t/2)*Fintype.card W≤((Finset.univ.filter (fun v=>H true v (u j))).card:ℝ):=by
      simpa only [hubNeighbourClass,ite_true,Fintype.card_subtype] using hclass (u j)
    apply hh.trans
    exact_mod_cast Finset.card_le_card (show Finset.univ.filter (fun v=>H true v (u j))⊆
      Finset.univ.filter (fun v=>H false v (u j)∨H true v (u j)) from by
        intro v hv;exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr (Finset.mem_filter.mp hv).2⟩)
  · intro j
    simpa only [Finset.card_univ,Nat.add_assoc,Nat.reduceAdd] using hcounts.1 (u j)
  · intro j i v v' hv _ _
    simpa only [Finset.card_univ] using hcounts.2 (u j) i v v' hv
  · intro j C
    exact ⟨successor_seed_positive_lower hw (by omega) hnpos hDlo hDhi
      pr kr sr pstar hpstar hp hk hs hp1' hk1 hs1 haLo.le hB C.val
      (marked_sample_cycle_valid P ρ (3*d) (r+4) _ (hubCycleAsMarked (u j) C)) C.property.1.1,
      (successor_seed_nonneg_upper hw (by omega) hnpos hDlo hDhi
        pr kr sr pstar hpstar hp hk hs hp1' hk1 hs1 hB C.val).2⟩
  · intro j v hv
    simpa only [hubCycleAsMarked] using
      marked_sample_hub_degree_error P ρ d (r+4) D pr kr sr η weight σ H hload (u j) (hdis j) v hv

end Oberwolfach
