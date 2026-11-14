module

public import Oberwolfach.OrdinaryGeneralSameSampleProbability
public import Oberwolfach.MixedFreshPairingParentInsideRoots
public import Oberwolfach.BoundaryReserveSupportEvent

@[expose] public section
/-! A genuine pairing parent gives fresh pairings and boundary support
    on one physical-edge retention sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_fresh_pairing_probability_uniform
    (m:ℕ) (hm:3≤m) (γ κ b B p₀ a:ℝ)
    (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B) (hp₀:0<p₀) (hp₀1:p₀≤1) (ha:0<a) (ha1:a≤1):
    ∃ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧
    ∀(b₀:ℕ) (p:ℝ) (hp:0<p) (hp1:p≤1) (ρ:ℝ) (hρ:0<ρ) (εsup:ℝ) (hsup:0<εsup) (q:ℕ),∃N:ℕ,
    ∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (X:Finset V) (Z:Finset U)
      (tw:{v:V // v∉X}→ℝ),
    ∀(data:MixedFreshPairingParentInsideRoots m b₀ γ κ b B p₀ a ε η Qfactor F
      (ordinaryPhysicalGraph Qfactor Hfactor) (ordinaryPhysicalGraph F (fun _ _=>False))
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H Z X)
      (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr) tw),
    let law:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-1/(Fintype.card V:ℝ)^q-1/(Fintype.card (V⊕U):ℝ)^q≤
      law.probability (OrdinaryGeneralFreshPairingSample m Q Qfactor F H Hfactor X Z p ρ ζ εsup) :=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hfactor⟩:=mixed_fresh_pairing_probability_from_inside_parent m hm γ κ b B p₀ a
    hγ hκ hb hB hp₀ hp₀1 ha ha1
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro b₀ p hp hp1 ρ hρ εsup hsup q
  obtain ⟨Nf,hNf⟩:=hfactor b₀ p hp hp1 ρ hρ q
  obtain ⟨Ns,hNs⟩:=boundary_reserve_support_high_probability εsup hsup q
  refine ⟨max 2 (max Nf Ns),?_⟩
  intro V U _ _ _ _ hn hu Q Qfactor F H Hfactor X Z tw data law
  have hnW:Fintype.card V≤Fintype.card (V⊕U):=Fintype.card_le_of_injective Sum.inl Sum.inl_injective
  have hJ:Fintype.card {u:U // u∉Z}≤(Fintype.card V)^2:=by
    have hh:Fintype.card {u:U // u∉Z}≤Fintype.card U:=Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    nlinarith
  have hI:Fintype.card {v:V // v∉X}≤(Fintype.card (V⊕U))^2:=by
    have hh:Fintype.card {v:V // v∉X}≤Fintype.card V:=Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    nlinarith
  have hf:=hNf V (V⊕U) {u:U // u∉Z} {v:V // v∉X} (Sym2 (V⊕U))
    (by omega) hJ hI Qfactor F (ordinaryPhysicalGraph Qfactor Hfactor)
    (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
    (ordinaryBoundaryHubSet H Z X) (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl)
    (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr)
    (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val)) tw data
  have hs:=hNs (V⊕U) (by omega) (ordinaryBoundaryGraph Q H X Z) p hp.le hp1
  have hi:=finiteLaw_intersection_lower law _ _ (1/(Fintype.card V:ℝ)^q)
    (1/(Fintype.card (V⊕U):ℝ)^q) hf hs
  apply hi.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  exact ⟨hσ.2,hσ.1⟩
end Oberwolfach
