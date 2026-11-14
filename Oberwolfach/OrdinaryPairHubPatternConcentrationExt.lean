module

public import Oberwolfach.OrdinaryPairHubCoordinateGeometry
public import Oberwolfach.OrdinaryRawIntervalSampling
public import Oberwolfach.OrdinaryPatternSupportedConcentration

@[expose] public section

/-! Simultaneous concentration of fixed wheel coefficients on all sampled
pairwise common-spoke classes. The expectation is for the original raw law;
no uniformity on arbitrary outcome-dependent domains is asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_pair_hub_pattern_load_common_event_ext
    (P F:SimpleGraph V) (π:Equiv.Perm V) (r d:ℕ) (hr:2≤r) (hd:2≤d)
    (hn:0<Fintype.card V) (w:OrdinaryWheel P F (fun (_:V) (_:Unit)=>True) r→ℝ)
    (B:ℝ) (hB:0<B) (hw:∀ W,0≤w W∧w W≤B/(Fintype.card V:ℝ)^(r-1))
    (ρ:Sym2 V→ℝ) (hρ:∀ e,0≤ρ e) (hρ1:∀ e,ρ e≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
    (hS:∀ u,∑ j,s u j ≤ intervalUncoveredProbability d (∑ g,q u g))
    (j:Color) (t:ℝ) (ht:0<t):
    let μ:=FiniteLaw.pi (rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS)
    let C:ℝ:=2*(4*(d:ℝ)+3)
    let err:=(Fintype.card (Sym2 V⊕(V×Unit)):ℝ)*
      (2*Real.exp (-2*t^2/(C^2*((r:ℝ)^4*B/Fintype.card V)*(2*r)*((r:ℝ)^2*B))));
    1-(Fintype.card (U×U):ℝ)*err≤μ.probability (fun σ=>∀ u u' root,
      |resourcePatternLoad ordinaryWheelResources w (fun _ _=>true) root (ordinaryResourceState (rawWheelGraph P σ) (ordinaryPairHubSpokes π d σ j u u'))-
        μ.expectation (fun τ=>resourcePatternLoad ordinaryWheelResources w (fun _ _=>true) root (ordinaryResourceState (rawWheelGraph P τ) (ordinaryPairHubSpokes π d τ j u u')))|<t) := by
  intro μ C err
  have hC:0<C:=by dsimp [C];positivity
  have hunit:Fintype.card Unit≤Fintype.card V:=by simp only [Fintype.card_unit]; omega
  let Good:=fun a:U×U=>fun σ:RawWheelOutcome V U Γ Color=>∀ root,
    |resourcePatternLoad ordinaryWheelResources w (fun _ _=>true) root (ordinaryResourceState (rawWheelGraph P σ) (ordinaryPairHubSpokes π d σ j a.1 a.2))-
      μ.expectation (fun τ=>resourcePatternLoad ordinaryWheelResources w (fun _ _=>true) root (ordinaryResourceState (rawWheelGraph P τ) (ordinaryPairHubSpokes π d τ j a.1 a.2)))|<t
  have hpair (a:U×U):1-err≤μ.probability (Good a):=by
    obtain ⟨hread,haffect⟩:=ordinary_pair_hub_coordinates_bounds (V:=V) (U:=U) π d a.1 a.2
    have hh:=ordinaryPatternLoad_supported_common_event (V:=V) (U:=Unit) (E:=RawWheelCoordinate V U) P F (fun (_:V) (_:Unit)=>True) r hr hn hunit w B hB.le hw
      (rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS)
      (rawWheelGraph P) (fun σ=>ordinaryPairHubSpokes π d σ j a.1 a.2)
      (ordinaryPairHubCoordinates π d a.1 a.2)
      (ordinary_pair_hub_resource_supported P π d j a.1 a.2) C hC hB
      (by intro z;dsimp [C];exact_mod_cast hread z) (by intro z;dsimp [C];exact_mod_cast haffect z) t ht
    convert hh using 1 <;> congr!
  have hh:=finiteLaw_common_event_lower μ Finset.univ (fun a σ=>¬Good a σ) (fun _=>err) (by
    intro a ha
    have hc:=finiteLaw_probability_compl μ (Good a)
    linarith only [hpair a,hc])
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies,
    not_not,Good,Prod.forall] using hh
end Oberwolfach
