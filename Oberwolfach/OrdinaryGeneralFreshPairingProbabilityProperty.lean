module

public import Oberwolfach.OrdinaryGeneralFreshPairingProbabilityUniform

@[expose] public section
/-! Name the fresh pairing probability with tolerances fixed before the
    later conflict bound and the retention probability. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryGeneralFreshPairingProbabilityProperty (m:ℕ) (γ κ b B p₀ a ε η ζ:ℝ):Prop :=
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
      law.probability (OrdinaryGeneralFreshPairingSample m Q Qfactor F H Hfactor X Z p ρ ζ εsup)

theorem ordinary_general_fresh_pairing_probability_property
    (m:ℕ) (hm:3≤m) (γ κ b B p₀ a:ℝ)
    (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B) (hp₀:0<p₀) (hp₀1:p₀≤1) (ha:0<a) (ha1:a≤1):
    ∃ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧
      OrdinaryGeneralFreshPairingProbabilityProperty m γ κ b B p₀ a ε η ζ :=by
  exact ordinary_general_fresh_pairing_probability_uniform m hm γ κ b B p₀ a
    hγ hκ hb hB hp₀ hp₀1 ha ha1
end Oberwolfach
