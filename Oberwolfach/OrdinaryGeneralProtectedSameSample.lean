module

public import Oberwolfach.OrdinaryRootFirstGeneralPairingSameSample
public import Oberwolfach.OrdinaryGeneralRootFirstMargins

@[expose] public section
/-! A root-first cleanup, its local tests, fresh pairings and a protected
    general-wheel cover-down all use the same expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_protected_same_sample
    (m b₀:ℕ) (hm:3≤m) (γ κ b B p₀ a:ℝ)
    (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B) (hp₀:0<p₀) (hp₀1:p₀≤1) (ha:0<a) (ha1:a≤1):
    ∃ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧
    ∀(p:ℝ) (hp:0<p) (hp1:p≤1) (ρ:ℝ) (hρ:0<ρ) (q:ℕ) (εsup:ℝ) (hsup:0<εsup),∃N:ℕ,
    ∀(V U Ω Γ Color:Type) [Fintype V] [Fintype U] [Fintype Ω] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (err:ℝ)
      (P Q Qfactor F:Ω→SimpleGraph V) (H Hfactor:Ω→V→U→Prop) (X T:Ω→Finset V) (Z W:Ω→Finset U)
      (π:Equiv.Perm V) (d:ℕ) (ηcover ell t ν βe βh budget:ℝ)
      (D:∀ω,OrdinaryRootCoverData (Q ω) (F ω) (H ω) (X ω) (T ω) (Z ω) (W ω) (m+1) ηcover ell)
      (tw:∀ω,{v:V // v∉X ω}→ℝ) (pR pH density tR tH Ledit βe₀ βh₀:ℝ)
      (s:U→Color→ℝ) (j:Color) (raw:Ω→RawWheelOutcome V U Γ Color),
    0≤t→
    (∀ω,E ω→Disjoint (Q ω) (F ω))→
    (∀ω,E ω→∀v,(Q ω).degree v=2*(Finset.univ.filter (H ω v)).card)→
    (∀ω,E ω→∀u,(m+1)∣(Finset.univ.filter (fun v=>H ω v u)).card)→
    (∀ω,E ω→OrdinaryCleanupParentProfiles (P ω) (Q ω) (F ω) (H ω) π d (X ω) (Z ω)
      pR pH density tR tH Ledit βe₀ βh₀ s j (raw ω))→
    βe*Fintype.card (V⊕U)+3*max ηcover ell≤βe₀*Fintype.card (V⊕U)→
    βh*Fintype.card (V⊕U)+2*ell≤βh₀*Fintype.card (V⊕U)→
    (∀ω,E ω→MixedFreshPairingParentInsideRoots m b₀ γ κ b B p₀ a ε η (Qfactor ω) (F ω)
      (ordinaryPhysicalGraph (Qfactor ω) (Hfactor ω)) (ordinaryPhysicalGraph (F ω) (fun _ _=>False))
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet (H ω) (Z ω) (X ω))
      (fun i=>(ordinaryBoundaryRimSet (Q ω) (X ω) i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet (H ω) (X ω) (Z ω) i).image Sum.inr) (tw ω))→
    (∀ω,E ω→∀σ (O:OrdinaryRootFirstCleanupOutcome (Q ω) (F ω) (H ω) (X ω) (T ω) (Z ω) (W ω)
      (m+1) ηcover ell t ν (D ω) σ),
      BoundaryReserveSupportGood (ordinaryBoundaryGraph (Q ω) (H ω) (X ω) (Z ω)) p εsup σ→
      OrdinaryGeneralRootFirstMargins m (Q ω) (Qfactor ω) (F ω) (H ω) (Hfactor ω) (X ω) (T ω) (Z ω) (W ω)
        ηcover ell t ν (D ω) σ O p ρ ζ εsup βe budget)→
    let law:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-err≤(μ.sigma (fun _=>law)).probability (fun z=>E z.1 ∧
      Nonempty (OrdinaryRootFirstCleanupOutcome (Q z.1) (F z.1) (H z.1) (X z.1) (T z.1) (Z z.1) (W z.1)
        (m+1) ηcover ell t ν (D z.1) z.2) ∧
      OrdinaryBoundaryExtensionGood (Q z.1\(D z.1).rim)
        (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (X z.1) βe p z.2 ∧
      OrdinaryBoundaryHubPairGood (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (Z z.1) βh p z.2)→
    ((err+1/(Fintype.card (V⊕U):ℝ)^q)+1/(Fintype.card V:ℝ)^q)<1→
    ∃z,0<(μ.sigma (fun _=>law)).mass z ∧ E z.1 ∧
      OrdinaryProtectedHostCoverDownResult (Q z.1) (F z.1) (H z.1) (X z.1) (T z.1) (Z z.1) (W z.1)
        (m+1) budget budget :=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hmain⟩:=ordinary_root_first_general_pairing_same_sample_witness m b₀ hm γ κ b B p₀ a
    hγ hκ hb hB hp₀ hp₀1 ha ha1
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 ρ hρ q εsup hsup
  obtain ⟨N,hN⟩:=hmain p hp hp1 ρ hρ q εsup hsup
  refine ⟨N,?_⟩
  intro V U Ω Γ Color _ _ _ _ _ _ _ hn hu μ E err P Q Qfactor F H Hfactor X T Z W π d ηcover ell t ν βe βh budget
    D tw pR pH density tR tH Ledit βe₀ βh₀ s j raw ht hQF hbal hdiv hprofile hmE hmH hparent hnum law hprior hsmall
  obtain ⟨z,hmass,hE,⟨O⟩,hext,hhub,hsupport,hpair⟩:=
    hN V U Ω hn hu μ E err Q Qfactor F H Hfactor X T Z W ηcover ell t ν βe βh D tw hparent hprior hsmall
  refine ⟨z,hmass,hE,?_⟩
  exact ordinary_general_root_first_protected_of_margins m hm (P z.1) (Q z.1) (Qfactor z.1) (F z.1)
    (H z.1) (Hfactor z.1) π d (X z.1) (T z.1) (Z z.1) (W z.1) ηcover ell t ν (D z.1) z.2 O
    pR pH p density tR tH Ledit βe₀ βh₀ βe βh ρ ζ εsup budget s j (raw z.1) ht hp.le
    (hQF z.1 hE) (hbal z.1 hE) (hdiv z.1 hE) (hprofile z.1 hE) hmE hmH hsupport hext hhub hpair (hnum z.1 hE z.2 O hsupport)
end Oberwolfach
