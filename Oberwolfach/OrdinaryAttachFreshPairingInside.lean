module

public import Oberwolfach.MixedFreshPairingParentInsideRoots
public import Oberwolfach.FiniteLawAttachConditionalEvent
public import Oberwolfach.OrdinaryBoundaryFactorClassesAfterPacking

@[expose] public section
/-! Attach the fresh boundary pairing event to any earlier event using the
same physical coins, conditional on the chosen inside-parent data. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 8192
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_attach_fresh_pairing_inside
    (m b₀:ℕ) (hm:3≤m) (γ κ b B p₀ a:ℝ)
    (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B) (hp₀:0<p₀) (hp₀1:p₀≤1) (ha:0<a) (ha1:a≤1):
    ∃ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧
    ∀(p:ℝ) (hp:0<p) (hp1:p≤1) (ρ:ℝ) (hρ:0<ρ) (q:ℕ),∃N:ℕ,
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
    1-(e+1/(Fintype.card V:ℝ)^q)≤(μ.sigma (fun _=>law)).probability (fun z=>Prior z ∧
      MixedFreshPairingAvoidingEvent m p ρ ζ (Q z.1) (F z.1)
        (ordinaryPhysicalGraph (Q z.1) (H z.1)) (ordinaryPhysicalGraph (F z.1) (fun _ _=>False))
        (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet (H₀ z.1) (Z z.1) (X z.1))
        (fun i=>(ordinaryBoundaryRimSet (Q₀ z.1) (X z.1) i).image Sum.inl)
        (fun i=>(ordinaryBoundaryRowSet (H₀ z.1) (X z.1) (Z z.1) i).image Sum.inr)
        (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val)) z.2):=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hfactor⟩:=mixed_fresh_pairing_probability_from_inside_parent m hm γ κ b B p₀ a
    hγ hκ hb hB hp₀ hp₀1 ha ha1
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 ρ hρ q
  obtain ⟨N,hN⟩:=hfactor b₀ p hp hp1 ρ hρ q
  refine ⟨max 2 N,?_⟩
  intro V U Ω _ _ _ _ _ hn hu μ E e Prior Q₀ Q F H₀ H X Z t data law hPrior hPE
  have hn1:1≤Fintype.card V:=by omega
  have hnW:Fintype.card V≤Fintype.card (V⊕U):=Fintype.card_le_of_injective Sum.inl Sum.inl_injective
  have hJ (s:Ω):Fintype.card {u:U // u∉Z s}≤(Fintype.card V)^2:=by
    have hh:Fintype.card {u:U // u∉Z s}≤Fintype.card U:=Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    nlinarith
  have hI (s:Ω):Fintype.card {v:V // v∉X s}≤(Fintype.card (V⊕U))^2:=by
    have hh:Fintype.card {v:V // v∉X s}≤Fintype.card V:=Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    nlinarith
  let Good:=fun s σ=>MixedFreshPairingAvoidingEvent m p ρ ζ (Q s) (F s)
      (ordinaryPhysicalGraph (Q s) (H s)) (ordinaryPhysicalGraph (F s) (fun _ _=>False))
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet (H₀ s) (Z s) (X s))
      (fun i=>(ordinaryBoundaryRimSet (Q₀ s) (X s) i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet (H₀ s) (X s) (Z s) i).image Sum.inr)
      (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val)) σ
  have hs:∀s,E s→1-1/(Fintype.card V:ℝ)^q≤law.probability (Good s):=by
    intro s hs
    exact hN V (V⊕U) {u:U // u∉Z s} {v:V // v∉X s} (Sym2 (V⊕U))
      (by omega) (hJ s) (hI s) (Q s) (F s) (ordinaryPhysicalGraph (Q s) (H s))
      (ordinaryPhysicalGraph (F s) (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet (H₀ s) (Z s) (X s))
      (fun i=>(ordinaryBoundaryRimSet (Q₀ s) (X s) i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet (H₀ s) (X s) (Z s) i).image Sum.inr)
      (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val)) (t s) (data s hs)
  exact finiteLaw_attach_conditional_event μ (fun _=>law) E Prior Good e _ (by positivity) hPrior hPE hs
end Oberwolfach
