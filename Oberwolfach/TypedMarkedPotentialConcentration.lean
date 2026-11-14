module

public import Oberwolfach.TypedMarkedLoadBounds

@[expose] public section

/-! Concentration for all fixed typed potential roots. Primitive-coordinate
supports may overlap between different resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E K : Type*} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
  {H₀ Hₖ : V → U → Prop}
  (hm : 3≤m) (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
  (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
  (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
include hm hn hu hB hw

theorem typedMarkedPotentialLoad_supported_tail
    {J : Type*} [Fintype J] [DecidableEq J]
    {Base : J → Type*} [∀ e,Fintype (Base e)]
    (μ : ∀ e,FiniteLaw (Base e))
    (Q : (∀ e,Base e) → E⊕K → Prop) (H : (∀ e,Base e) → Bool → V → U → Prop)
    (S : (E⊕K)⊕(Bool×V×U) → Finset J)
    (hs : ∀ a σ τ,(∀ e∈S a,σ e=τ e) → typedMarkedResourceState (Q σ) (H σ) a=typedMarkedResourceState (Q τ) (H τ) a)
    (Bloc : ℝ) (hBloc : 0<Bloc) (hBp : 0<B)
    (hread : ∀ a,((S a).card:ℝ)≤Bloc)
    (haffect : ∀ e,((Finset.univ.filter (fun a=>e∈S a)).card:ℝ)≤Bloc)
    (root : (E⊕K)⊕(Bool×V×U)) (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi μ).probability (fun σ=>t≤
      |typedMarkedPotentialLoad w (Q σ) (H σ) root-
        (FiniteLaw.pi μ).expectation (fun τ=>typedMarkedPotentialLoad w (Q τ) (H τ) root)|)≤
      2*Real.exp (-2*t^2/(Bloc^2*(((m:ℝ)+1)^4*B/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B))) := by
  have hn0 : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have hr0 : (0:ℝ)<(m:ℝ)+1 := by positivity
  have hh := resourcePatternLoad_supported_tail μ typedMarkedOccurrenceResources w (fun W=>(hw W).1)
    (fun _ _=>true) S (fun σ=>typedMarkedResourceState (Q σ) (H σ)) hs Bloc hBloc hread haffect root
    (2*((m:ℝ)+1)) (((m:ℝ)+1)^2*B) (((m:ℝ)+1)^4*B/Fintype.card V) (by positivity) (by positivity) (by positivity)
    (by
      intro W _
      have hc := Finset.card_le_card (Finset.sdiff_subset : typedMarkedOccurrenceResources W\{root}⊆typedMarkedOccurrenceResources W)
      exact_mod_cast hc.trans (typedMarkedOccurrenceResources_card W))
    (typedMarkedOccurrenceResources_load_bound (by omega) hn hu w B hB hw root)
    (typedMarkedOmittedPair_uniform_bound hm hn hu w B hB hw root) t ht
  simpa only [← typedMarkedPotentialLoad_eq_pattern] using hh


theorem typedMarkedPotentialLoad_supported_common_event
    {J : Type*} [Fintype J] [DecidableEq J]
    {Base : J → Type*} [∀ e,Fintype (Base e)]
    (μ : ∀ e,FiniteLaw (Base e))
    (Q : (∀ e,Base e) → E⊕K → Prop) (H : (∀ e,Base e) → Bool → V → U → Prop)
    (S : (E⊕K)⊕(Bool×V×U) → Finset J)
    (hs : ∀ a σ τ,(∀ e∈S a,σ e=τ e) → typedMarkedResourceState (Q σ) (H σ) a=typedMarkedResourceState (Q τ) (H τ) a)
    (Bloc : ℝ) (hBloc : 0<Bloc) (hBp : 0<B)
    (hread : ∀ a,((S a).card:ℝ)≤Bloc)
    (haffect : ∀ e,((Finset.univ.filter (fun a=>e∈S a)).card:ℝ)≤Bloc)
    (t : ℝ) (ht : 0<t) :
    1-(Fintype.card ((E⊕K)⊕(Bool×V×U)):ℝ)*
      (2*Real.exp (-2*t^2/(Bloc^2*(((m:ℝ)+1)^4*B/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B))))≤
      (FiniteLaw.pi μ).probability (fun σ=>∀ root,
        |typedMarkedPotentialLoad w (Q σ) (H σ) root-
          (FiniteLaw.pi μ).expectation (fun τ=>typedMarkedPotentialLoad w (Q τ) (H τ) root)|<t) := by
  have hh := finiteLaw_common_event_lower (FiniteLaw.pi μ) Finset.univ
    (fun root σ=>t≤|typedMarkedPotentialLoad w (Q σ) (H σ) root-
      (FiniteLaw.pi μ).expectation (fun τ=>typedMarkedPotentialLoad w (Q τ) (H τ) root)|)
    (fun _=>2*Real.exp (-2*t^2/(Bloc^2*(((m:ℝ)+1)^4*B/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B))))
    (fun root _=>typedMarkedPotentialLoad_supported_tail hm hn hu w B hB hw
      μ Q H S hs Bloc hBloc hBp hread haffect root t ht)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies,not_le] using hh

end Oberwolfach
