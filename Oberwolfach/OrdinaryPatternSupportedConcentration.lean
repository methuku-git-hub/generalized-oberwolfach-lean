module

public import Oberwolfach.OrdinaryPotentialConcentration

@[expose] public section

/-! The wheel pattern-load concentration in its explicit representation,
without an elaboration-time conversion to the concrete load abbreviation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (P F : SimpleGraph V) (Hbase : V → U → Prop) (r : ℕ)
    (hr : 2≤r) (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (w : OrdinaryWheel P F Hbase r → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^(r-1))
include hr hn hu hB hw

theorem ordinaryPatternLoad_supported_tail
    {E : Type*} [Fintype E] [DecidableEq E]
    {Base : E → Type*} [∀ e,Fintype (Base e)]
    (μ : ∀ e,FiniteLaw (Base e))
    (Q : (∀ e,Base e) → SimpleGraph V) (H : (∀ e,Base e) → V → U → Prop)
    (S : Sym2 V⊕(V×U) → Finset E)
    (hs : ∀ a σ τ,(∀ e∈S a,σ e=τ e) → ordinaryResourceState (Q σ) (H σ) a=ordinaryResourceState (Q τ) (H τ) a)
    (Bloc : ℝ) (hBloc : 0<Bloc) (hBp : 0<B)
    (hread : ∀ a,((S a).card:ℝ)≤Bloc)
    (haffect : ∀ e,((Finset.univ.filter (fun a=>e∈S a)).card:ℝ)≤Bloc)
    (root : Sym2 V⊕(V×U)) (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi μ).probability (fun σ=>t≤
      |resourcePatternLoad ordinaryWheelResources w (fun _ _=>true) root (ordinaryResourceState (Q σ) (H σ))-
        (FiniteLaw.pi μ).expectation (fun τ=>resourcePatternLoad ordinaryWheelResources w (fun _ _=>true) root (ordinaryResourceState (Q τ) (H τ)))|)≤
      2*Real.exp (-2*t^2/(Bloc^2*((r:ℝ)^4*B/Fintype.card V)*(2*r)*((r:ℝ)^2*B))) := by
  have hn0 : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have hr0 : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have hh := resourcePatternLoad_supported_tail μ ordinaryWheelResources w (fun W=>(hw W).1)
    (fun _ _=>true) S (fun σ=>ordinaryResourceState (Q σ) (H σ)) hs Bloc hBloc hread haffect root
    (2*r) ((r:ℝ)^2*B) ((r:ℝ)^4*B/Fintype.card V) (by positivity) (by positivity) (by positivity)
    (by
      intro W _
      have hc := Finset.card_le_card (Finset.sdiff_subset : ordinaryWheelResources W\{root}⊆ordinaryWheelResources W)
      rw [ordinaryWheelResources_card] at hc
      exact_mod_cast hc)
    (ordinary_wheel_resource_load_bound P F Hbase r hr hn hu w B hB hw root)
    (ordinary_wheel_omitted_pair_bound P F Hbase r hr hn hu w B hB hw root) t ht
  exact hh


theorem ordinaryPatternLoad_supported_common_event
    {E : Type*} [Fintype E] [DecidableEq E]
    {Base : E → Type*} [∀ e,Fintype (Base e)]
    (μ : ∀ e,FiniteLaw (Base e))
    (Q : (∀ e,Base e) → SimpleGraph V) (H : (∀ e,Base e) → V → U → Prop)
    (S : Sym2 V⊕(V×U) → Finset E)
    (hs : ∀ a σ τ,(∀ e∈S a,σ e=τ e) → ordinaryResourceState (Q σ) (H σ) a=ordinaryResourceState (Q τ) (H τ) a)
    (Bloc : ℝ) (hBloc : 0<Bloc) (hBp : 0<B)
    (hread : ∀ a,((S a).card:ℝ)≤Bloc)
    (haffect : ∀ e,((Finset.univ.filter (fun a=>e∈S a)).card:ℝ)≤Bloc)
    (t : ℝ) (ht : 0<t) :
    1-(Fintype.card (Sym2 V⊕(V×U)):ℝ)*
      (2*Real.exp (-2*t^2/(Bloc^2*((r:ℝ)^4*B/Fintype.card V)*(2*r)*((r:ℝ)^2*B))))≤
      (FiniteLaw.pi μ).probability (fun σ=>∀ root,
        |resourcePatternLoad ordinaryWheelResources w (fun _ _=>true) root (ordinaryResourceState (Q σ) (H σ))-
          (FiniteLaw.pi μ).expectation (fun τ=>resourcePatternLoad ordinaryWheelResources w (fun _ _=>true) root (ordinaryResourceState (Q τ) (H τ)))|<t) := by
  have hh := finiteLaw_common_event_lower (FiniteLaw.pi μ) Finset.univ
    (fun root σ=>t≤|resourcePatternLoad ordinaryWheelResources w (fun _ _=>true) root (ordinaryResourceState (Q σ) (H σ))-
      (FiniteLaw.pi μ).expectation (fun τ=>resourcePatternLoad ordinaryWheelResources w (fun _ _=>true) root (ordinaryResourceState (Q τ) (H τ)))|)
    (fun _=>2*Real.exp (-2*t^2/(Bloc^2*((r:ℝ)^4*B/Fintype.card V)*(2*r)*((r:ℝ)^2*B))))
    (fun root _=>ordinaryPatternLoad_supported_tail P F Hbase r hr hn hu w B hB hw
      μ Q H S hs Bloc hBloc hBp hread haffect root t ht)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies,not_le] using hh

end Oberwolfach
