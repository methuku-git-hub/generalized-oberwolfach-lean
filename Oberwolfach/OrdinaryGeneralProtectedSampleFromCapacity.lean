module

public import Oberwolfach.OrdinaryGeneralProtectedSameSample
public import Oberwolfach.OrdinaryGeneralMarginsFromCapacity
public import Oberwolfach.OrdinaryPairingParentHubSize

@[expose] public section
/-! The actual pairing parent and uniform completion capacity discharge
    the root-first general-wheel margins on the same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_protected_sample_from_capacity
    (m b₀:ℕ) (hm:3≤m) (γ κ b B p₀ a:ℝ)
    (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B) (hp₀:0<p₀) (hp₀1:p₀≤1) (ha:0<a) (ha1:a≤1):
    ∃ε ηf ζ:ℝ,0<ε ∧ 0<ηf ∧ 0<ζ ∧
    ∀(p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ) (εsup:ℝ) (hsup:0<εsup),∃N:ℕ,
    ∀(V U Ω Γ Color:Type) [Fintype V] [Fintype U] [Fintype Ω] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (err:ℝ)
      (P Q Qfactor F:Ω→SimpleGraph V) (H Hfactor:Ω→V→U→Prop) (X T:Ω→Finset V) (Z W:Ω→Finset U)
      (π:Equiv.Perm V) (d:ℕ) (τ ν ηrate ellrate βe βh rate:ℝ)
      (D:∀ω,OrdinaryRootCoverData (Q ω) (F ω) (H ω) (X ω) (T ω) (Z ω) (W ω) (m+1)
        (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U)))
      (tw:∀ω,{v:V // v∉X ω}→ℝ) (pR pH density tR tH Ledit βe₀ βh₀:ℝ)
      (s:U→Color→ℝ) (j:Color) (raw:Ω→RawWheelOutcome V U Γ Color),
    0≤τ→εsup≤p^2/4→τ+ν≤p^2/4→
    τ+ν+ellrate≤ζ*min (κ/2) 1*p/4→ν+ηrate≤ζ*min (κ/2) 1*p/4→
    p≤4*ζ*min (κ/2) 1→20*Real.sqrt (2*p)≤ζ*min (κ/2) 1/2→
    2≤ζ*min (κ/2) 1*p*Fintype.card (V⊕U)/4→
    (∀ω,E ω→Disjoint (Q ω) (F ω))→
    (∀ω,E ω→∀v,(Q ω).degree v=2*(Finset.univ.filter (H ω v)).card)→
    (∀ω,E ω→∀u,(m+1)∣(Finset.univ.filter (fun v=>H ω v u)).card)→
    (∀ω,E ω→OrdinaryCleanupParentProfiles (P ω) (Q ω) (F ω) (H ω) π d (X ω) (Z ω)
      pR pH density tR tH Ledit βe₀ βh₀ s j (raw ω))→
    βe*Fintype.card (V⊕U)+3*max (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U))≤βe₀*Fintype.card (V⊕U)→
    βh*Fintype.card (V⊕U)+2*(ellrate*Fintype.card (V⊕U))≤βh₀*Fintype.card (V⊕U)→
    (∀ω,E ω→MixedFreshPairingParentInsideRoots m b₀ γ κ b B p₀ a ε ηf (Qfactor ω) (F ω)
      (ordinaryPhysicalGraph (Qfactor ω) (Hfactor ω)) (ordinaryPhysicalGraph (F ω) (fun _ _=>False))
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet (H ω) (Z ω) (X ω))
      (fun i=>(ordinaryBoundaryRimSet (Q ω) (X ω) i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet (H ω) (X ω) (Z ω) i).image Sum.inr) (tw ω))→
    (∀ω,E ω→ ordinaryPhysicalGraph (Qfactor ω) (Hfactor ω)≤
      spanningRestriction (ordinaryPhysicalGraph (Q ω) (H ω)) (ordinaryInnerVertices (X ω) (Z ω)))→
    (∀ω,E ω→((T ω).card:ℝ)≤(βe/2)*Fintype.card (V⊕U))→
    ∀(Kcap Dmax:ℕ),0<Kcap→(2*p)*Fintype.card (V⊕U)≤(Dmax:ℝ)→
    ∀Lconf:ℝ,0≤Lconf→(∀ω,E ω→∀v,((F ω).degree v:ℝ)≤Lconf)→
    ((Fintype.card (V⊕U)*Dmax*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
      (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*Fintype.card (V⊕U))+2*((Kcap+Dmax:ℕ):ℝ))+
      (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < (βe/2)*Fintype.card (V⊕U)-3*(ν*Fintype.card (V⊕U))→
    ν*Fintype.card (V⊕U)+ηrate*Fintype.card (V⊕U)+2*((2*p)*Fintype.card (V⊕U))+
      ((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ)≤rate*Fintype.card (V⊕U)→
    let law:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-err≤(μ.sigma (fun _=>law)).probability (fun z=>E z.1 ∧
      Nonempty (OrdinaryRootFirstCleanupOutcome (Q z.1) (F z.1) (H z.1) (X z.1) (T z.1) (Z z.1)
        (W z.1) (m+1) (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U))
        (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) (D z.1) z.2) ∧
      OrdinaryBoundaryExtensionGood (Q z.1\(D z.1).rim)
        (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (X z.1) βe p z.2 ∧
      OrdinaryBoundaryHubPairGood (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (Z z.1) βh p z.2)→
    ((err+1/(Fintype.card (V⊕U):ℝ)^q)+1/(Fintype.card V:ℝ)^q)<1→
    ∃z,0<(μ.sigma (fun _=>law)).mass z ∧ E z.1 ∧
      OrdinaryProtectedHostCoverDownResult (Q z.1) (F z.1) (H z.1) (X z.1) (T z.1) (Z z.1) (W z.1)
        (m+1) (rate*Fintype.card (V⊕U)) (rate*Fintype.card (V⊕U)) :=by
  obtain ⟨ε,ηf,ζ,hε,hηf,hζ,hmain⟩:=ordinary_general_protected_same_sample m b₀ hm γ κ b B p₀ a
    hγ hκ hb hB hp₀ hp₀1 ha ha1
  refine ⟨ε,ηf,ζ,hε,hηf,hζ,?_⟩
  intro p hp hp1 q εsup hsup
  obtain ⟨N,hN⟩:=hmain p hp hp1 (2*p) (by positivity) q εsup hsup
  refine ⟨N,?_⟩
  intro V U Ω Γ Color _ _ _ _ _ _ _ hn hu μ E err P Q Qfactor F H Hfactor X T Z W π d τ ν ηrate ellrate βe βh rate
    D tw pR pH density tR tH Ledit βe₀ βh₀ s j raw hτ hεsup hsupport hclass hblock hpκ hsqrt horder
    hQF hbal hdiv hprofile hmE hmH hparent hbase hT Kcap Dmax hKcap hDmax Lconf hLconf hF hcompletion hcost law hprior hsmall
  have hκ':0<min (κ/2) 1:=lt_min (by positivity) (by norm_num)
  have hκone:min (κ/2) 1≤1:=min_le_right _ _
  have hn':0≤(Fintype.card (V⊕U):ℝ):=by positivity
  have hnum:∀ω,E ω→∀σ (O:OrdinaryRootFirstCleanupOutcome (Q ω) (F ω) (H ω) (X ω) (T ω) (Z ω) (W ω)
      (m+1) (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U))
      (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) (D ω) σ),
      BoundaryReserveSupportGood (ordinaryBoundaryGraph (Q ω) (H ω) (X ω) (Z ω)) p εsup σ→
      OrdinaryGeneralRootFirstMargins m (Q ω) (Qfactor ω) (F ω) (H ω) (Hfactor ω) (X ω) (T ω) (Z ω) (W ω)
        (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U))
        (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) (D ω) σ O p (2*p) ζ εsup βe (rate*Fintype.card (V⊕U)):=by
    intro ω hE σ O hsample
    have hY:=ordinary_pairing_parent_hub_size m b₀ γ κ b B p₀ a ε ηf hκ.le
      (Q ω) (Qfactor ω) (F ω) (H ω) (Hfactor ω) (X ω) (Z ω) (tw ω) (hparent ω hE) hu
    exact ordinary_general_margins_from_capacity m (Q ω) (Qfactor ω) (F ω) (H ω) (Hfactor ω) (X ω) (T ω) (Z ω) (W ω)
      p εsup τ ν ηrate ellrate (min (κ/2) 1) ζ βe rate (D ω) σ O hp hp1 hτ hκ' hκone hζ
      hεsup hsupport hclass hblock hpκ hsqrt horder hY hsample (hbase ω hE)
      Kcap Dmax hKcap hDmax Lconf hLconf (hF ω hE) (hT ω hE) hcompletion hcost
  exact hN V U Ω Γ Color hn hu μ E err P Q Qfactor F H Hfactor X T Z W π d
    (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U))
    (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) βe βh (rate*Fintype.card (V⊕U))
    D tw pR pH density tR tH Ledit βe₀ βh₀ s j raw (mul_nonneg hτ hn')
    hQF hbal hdiv hprofile hmE hmH hparent hnum hprior hsmall
end Oberwolfach
