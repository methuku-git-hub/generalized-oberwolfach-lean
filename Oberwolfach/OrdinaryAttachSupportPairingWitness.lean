module

public import Oberwolfach.OrdinaryAttachSupportAndPairing
public import Oberwolfach.FiniteLawPositiveEventWitness

@[expose] public section
/-! A prior event, support tests and fresh pairing have a positive-mass
joint witness on the very same expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 8192
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_attach_support_and_pairing_witness
    (m b₀:ℕ) (hm:3≤m) (γ κ b B p₀ a:ℝ)
    (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B) (hp₀:0<p₀) (hp₀1:p₀≤1) (ha:0<a) (ha1:a≤1):
    ∃ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧
    ∀(p:ℝ) (hp:0<p) (hp1:p≤1) (ρ:ℝ) (hρ:0<ρ) (q:ℕ) (εsup:ℝ) (hsup:0<εsup),∃N:ℕ,
    ∀(V U Ω:Type) [Fintype V] [Fintype U] [Fintype Ω] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e:ℝ) (Prior:(Σ _ : Ω,Sym2 (V⊕U)→Bool)→Prop)
      (Q₀ Q F:Ω→SimpleGraph V) (H₀ H:Ω→V→U→Prop) (X:Ω→Finset V) (Z:Ω→Finset U)
      (t:∀ω,{v:V // v∉X ω}→ℝ),
    (∀ω,E ω→MixedFreshPairingParentInsideRoots m b₀ γ κ b B p₀ a ε η (Q ω) (F ω)
      (ordinaryPhysicalGraph (Q ω) (H ω)) (ordinaryPhysicalGraph (F ω) (fun _ _=>False))
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet (H₀ ω) (Z ω) (X ω))
      (fun i=>(ordinaryBoundaryRimSet (Q₀ ω) (X ω) i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet (H₀ ω) (X ω) (Z ω) i).image Sum.inr) (t ω))→
    let law:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-e≤(μ.sigma (fun _=>law)).probability Prior→(∀z,Prior z→E z.1)→
    ((e+1/(Fintype.card (V⊕U):ℝ)^q)+1/(Fintype.card V:ℝ)^q)<1→
    ∃z,0<(μ.sigma (fun _=>law)).mass z ∧ Prior z ∧
      BoundaryReserveSupportGood (ordinaryBoundaryGraph (Q₀ z.1) (H₀ z.1) (X z.1) (Z z.1)) p εsup z.2 ∧
      MixedFreshPairingAvoidingEvent m p ρ ζ (Q z.1) (F z.1)
        (ordinaryPhysicalGraph (Q z.1) (H z.1)) (ordinaryPhysicalGraph (F z.1) (fun _ _=>False))
        (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet (H₀ z.1) (Z z.1) (X z.1))
        (fun i=>(ordinaryBoundaryRimSet (Q₀ z.1) (X z.1) i).image Sum.inl)
        (fun i=>(ordinaryBoundaryRowSet (H₀ z.1) (X z.1) (Z z.1) i).image Sum.inr)
        (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val)) z.2:=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hattach⟩:=ordinary_attach_support_and_pairing m b₀ hm γ κ b B p₀ a
    hγ hκ hb hB hp₀ hp₀1 ha ha1
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 ρ hρ q εsup hsup
  obtain ⟨N,hN⟩:=hattach p hp hp1 ρ hρ q εsup hsup
  refine ⟨N,?_⟩
  intro V U Ω _ _ _ _ _ hn hu μ E e Prior Q₀ Q F H₀ H X Z t hparent law hprior hPE hsmall
  have hp':=hN V U Ω hn hu μ E e Prior Q₀ Q F H₀ H X Z t hparent hprior hPE
  apply finiteLaw_positive_mass_witness_of_event
  linarith only [hp',hsmall]
end Oberwolfach
