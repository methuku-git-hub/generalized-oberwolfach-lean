module

public import Oberwolfach.OrdinaryAttachSupportPairingWitness
public import Oberwolfach.OrdinaryRootFirstCleanupReferenceWithTests

@[expose] public section
/-! A root-first cleanup, its local extension tests, reserve support and
fresh pairing can be selected on one positive-mass expanded outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 8192
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_root_first_general_pairing_same_sample_witness
    (m b₀:ℕ) (hm:3≤m) (γ κ b B p₀ a:ℝ)
    (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B) (hp₀:0<p₀) (hp₀1:p₀≤1) (ha:0<a) (ha1:a≤1):
    ∃ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧
    ∀(p:ℝ) (hp:0<p) (hp1:p≤1) (ρ:ℝ) (hρ:0<ρ) (q:ℕ) (εsup:ℝ) (hsup:0<εsup),∃N:ℕ,
    ∀(V U Ω:Type) [Fintype V] [Fintype U] [Fintype Ω] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (err:ℝ)
      (Q Qfactor F:Ω→SimpleGraph V) (H Hfactor:Ω→V→U→Prop) (X T:Ω→Finset V) (Z W:Ω→Finset U)
      (ηcover ell t ν βe βh:ℝ)
      (D:∀ω,OrdinaryRootCoverData (Q ω) (F ω) (H ω) (X ω) (T ω) (Z ω) (W ω) (m+1) ηcover ell)
      (tw:∀ω,{v:V // v∉X ω}→ℝ),
    (∀ω,E ω→MixedFreshPairingParentInsideRoots m b₀ γ κ b B p₀ a ε η (Qfactor ω) (F ω)
      (ordinaryPhysicalGraph (Qfactor ω) (Hfactor ω)) (ordinaryPhysicalGraph (F ω) (fun _ _=>False))
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet (H ω) (Z ω) (X ω))
      (fun i=>(ordinaryBoundaryRimSet (Q ω) (X ω) i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet (H ω) (X ω) (Z ω) i).image Sum.inr) (tw ω))→
    let law:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-err≤(μ.sigma (fun _=>law)).probability (fun z=>E z.1 ∧
      Nonempty (OrdinaryRootFirstCleanupOutcome (Q z.1) (F z.1) (H z.1) (X z.1) (T z.1) (Z z.1) (W z.1)
        (m+1) ηcover ell t ν (D z.1) z.2) ∧
      OrdinaryBoundaryExtensionGood (Q z.1\(D z.1).rim)
        (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (X z.1) βe p z.2 ∧
      OrdinaryBoundaryHubPairGood (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (Z z.1) βh p z.2)→
    ((err+1/(Fintype.card (V⊕U):ℝ)^q)+1/(Fintype.card V:ℝ)^q)<1→
    ∃z,0<(μ.sigma (fun _=>law)).mass z ∧ E z.1 ∧
      Nonempty (OrdinaryRootFirstCleanupOutcome (Q z.1) (F z.1) (H z.1) (X z.1) (T z.1) (Z z.1) (W z.1)
        (m+1) ηcover ell t ν (D z.1) z.2) ∧
      OrdinaryBoundaryExtensionGood (Q z.1\(D z.1).rim)
        (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (X z.1) βe p z.2 ∧
      OrdinaryBoundaryHubPairGood (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (Z z.1) βh p z.2 ∧
      BoundaryReserveSupportGood (ordinaryBoundaryGraph (Q z.1) (H z.1) (X z.1) (Z z.1)) p εsup z.2 ∧
      MixedFreshPairingAvoidingEvent m p ρ ζ (Qfactor z.1) (F z.1)
        (ordinaryPhysicalGraph (Qfactor z.1) (Hfactor z.1)) (ordinaryPhysicalGraph (F z.1) (fun _ _=>False))
        (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet (H z.1) (Z z.1) (X z.1))
        (fun i=>(ordinaryBoundaryRimSet (Q z.1) (X z.1) i).image Sum.inl)
        (fun i=>(ordinaryBoundaryRowSet (H z.1) (X z.1) (Z z.1) i).image Sum.inr)
        (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val)) z.2:=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hattach⟩:=ordinary_attach_support_and_pairing_witness m b₀ hm γ κ b B p₀ a
    hγ hκ hb hB hp₀ hp₀1 ha ha1
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 ρ hρ q εsup hsup
  obtain ⟨N,hN⟩:=hattach p hp hp1 ρ hρ q εsup hsup
  refine ⟨N,?_⟩
  intro V U Ω _ _ _ _ _ hn hu μ E err Q Qfactor F H Hfactor X T Z W ηcover ell t ν βe βh D tw hparent law hprior hsmall
  let Prior:=fun z:(Σ _ : Ω,Sym2 (V⊕U)→Bool)=>E z.1 ∧
      Nonempty (OrdinaryRootFirstCleanupOutcome (Q z.1) (F z.1) (H z.1) (X z.1) (T z.1) (Z z.1) (W z.1)
        (m+1) ηcover ell t ν (D z.1) z.2) ∧
      OrdinaryBoundaryExtensionGood (Q z.1\(D z.1).rim)
        (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (X z.1) βe p z.2 ∧
      OrdinaryBoundaryHubPairGood (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (Z z.1) βh p z.2
  obtain ⟨z,hmass,hprior',hsupport,hpair⟩:=hN V U Ω hn hu μ E err Prior Q Qfactor F H Hfactor X Z tw
    hparent hprior (by intro z hz;exact hz.1) hsmall
  exact ⟨z,hmass,hprior'.1,hprior'.2.1,hprior'.2.2.1,hprior'.2.2.2,hsupport,hpair⟩
end Oberwolfach
