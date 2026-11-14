module

public import Oberwolfach.OrdinaryTriangleFreshFactorProbability
public import Oberwolfach.OrdinaryDeepParentEarlyWeightsHierarchy

@[expose] public section
/-! Use the factor theorem's actual tolerances to choose the later deep-parent
    numeric parameters, keeping its earlier weights and densities fixed. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleFreshFactorProbabilityProperty (γ κ b B ε η ζ:ℝ):Prop :=
    ∀(p:ℝ) (hp:0<p) (hp1:p≤1) (εsup:ℝ) (hsup:0<εsup) (q:ℕ),∃N:ℕ,
    ∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (X:Finset V) (Z:Finset U),
    ∀(data:MixedFreshParentDataInsideRoots γ κ b B ε η Qfactor F
      (ordinaryPhysicalGraph Qfactor Hfactor) (ordinaryPhysicalGraph F (fun _ _=>False))
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H Z X)
      (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr)),
    let law:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-1/(Fintype.card V:ℝ)^q-1/(Fintype.card (V⊕U):ℝ)^q≤
      law.probability (OrdinaryTriangleFreshFactorSample Q Qfactor F H Hfactor X Z p ζ εsup)

theorem ordinary_deep_parent_fresh_probability_choices
    (pmin κe a K bcap Bmin:ℝ) (hp:0<pmin) (hκe:0<κe) (ha:0<a) (hK:0<K)
    (hbcap:0<bcap) (hBmin:0≤Bmin):
    ∃γ κ b B εf ηf ζ δparent εparent tpot lam:ℝ,
      0<γ ∧ 0<κ ∧ 0<b ∧ b≤bcap ∧ 0<B ∧ Bmin≤B ∧
      0<εf ∧ 0<ηf ∧ 0<ζ ∧
      OrdinaryDeepNumericParameters pmin κe a ηf εf K γ κ δparent εparent tpot lam b B ∧
      OrdinaryTriangleFreshFactorProbabilityProperty γ κ b B εf ηf ζ :=by
  obtain ⟨γ,κ,b,B,hγ,hκ,hb,hbcap',hB,hBmin',hNum⟩:=
    ordinary_deep_parent_early_weights_hierarchy pmin κe a K bcap Bmin hp hκe ha hK hbcap hBmin
  obtain ⟨εf,ηf,ζ,hεf,hηf,hζ,hprob⟩:=ordinary_triangle_fresh_factor_probability γ κ b B hγ hκ hb hB.le
  obtain ⟨δparent,εparent,tpot,lam,hNum⟩:=hNum ηf εf hηf hεf
  exact ⟨γ,κ,b,B,εf,ηf,ζ,δparent,εparent,tpot,lam,hγ,hκ,hb,hbcap',hB,hBmin',hεf,hηf,hζ,hNum,hprob⟩
end Oberwolfach
