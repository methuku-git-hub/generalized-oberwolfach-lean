module

public import Oberwolfach.TypedMarkedPotentialConcentration

@[expose] public section

/-! Spoke-root concentration does not require a bound on the total number
of hubs. This preserves fixed external hubs in the completion domains. -/
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

theorem typedMarkedSpoke_resource_load_bound
    (hn : 0<Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,w W≤B/(Fintype.card V:ℝ)^m) (j : Bool) (v : V) (u : U) :
    (∑ W,if Sum.inr (j,v,u)∈typedMarkedOccurrenceResources W then w W else 0)≤((m:ℝ)+1)^2*B := by
  have hh := marked_wheel_fixed_hub_event hn w B hB hw
    {v} (by simp) (by simp) u
    (fun W=>Sum.inr (j,v,u)∈typedMarkedOccurrenceResources W) (by
      intro W hW
      obtain ⟨i,hi⟩ := (typedMarkedOccurrenceResources_spoke W (j,v,u)).mp hW
      have hv : W.1.val i=v := congrArg (fun z : Bool×V×U=>z.2.1) hi
      have hu : W.2.val=u := congrArg (fun z : Bool×V×U=>z.2.2) hi
      refine ⟨?_,hu⟩
      intro x hx
      have hx' : x=v := Finset.mem_singleton.mp hx
      exact ⟨i,hv.trans hx'.symm⟩)
  simp only [Finset.card_singleton,pow_one,show 1-1=0 from rfl,pow_zero,div_one] at hh
  have hm0 : (0:ℝ)≤m := Nat.cast_nonneg _
  convert hh.trans (mul_le_mul_of_nonneg_right (by nlinarith : (m:ℝ)+1≤((m:ℝ)+1)^2) hB) using 1
  apply Finset.sum_congr rfl
  intro W _
  split_ifs <;> rfl

theorem typedMarkedSpoke_omitted_pair_bound
    (hm : 3≤m) (hn : 0<Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (j : Bool) (v : V) (u : U) (f : (E⊕K)⊕(Bool×V×U)) :
    resourceOmittedPairWeight typedMarkedOccurrenceResources w (Sum.inr (j,v,u)) f≤((m:ℝ)+1)^4*B/Fintype.card V := by
  have hnR : (1:ℝ)≤Fintype.card V := by exact_mod_cast (show 1≤Fintype.card V by omega)
  cases f with
  | inl f=>
    apply (typedMarkedPair_spoke_rim hm hn w B hB hw f j v u).trans
    split_ifs
    · exact le_refl _
    · apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
  | inr f=>
    apply (typedMarkedPair_spoke_spoke hm hn w B hB hw j f.1 v f.2.1 u f.2.2).trans
    split_ifs <;> first | exact le_refl _ | positivity

variable (hm : 3≤m) (hn : 0<Fintype.card V)
  (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
  (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
include hm hn hB hw

theorem typedMarkedSpoke_supported_tail
    {J : Type*} [Fintype J] [DecidableEq J]
    {Base : J → Type*} [∀ e,Fintype (Base e)]
    (μ : ∀ e,FiniteLaw (Base e))
    (Q : (∀ e,Base e) → E⊕K → Prop) (H : (∀ e,Base e) → Bool → V → U → Prop)
    (S : (E⊕K)⊕(Bool×V×U) → Finset J)
    (hs : ∀ a σ τ,(∀ e∈S a,σ e=τ e) → typedMarkedResourceState (Q σ) (H σ) a=typedMarkedResourceState (Q τ) (H τ) a)
    (Bloc : ℝ) (hBloc : 0<Bloc) (hBp : 0<B)
    (hread : ∀ a,((S a).card:ℝ)≤Bloc)
    (haffect : ∀ e,((Finset.univ.filter (fun a=>e∈S a)).card:ℝ)≤Bloc)
    (j : Bool) (v : V) (u : U) (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi μ).probability (fun σ=>t≤
      |typedMarkedPotentialLoad w (Q σ) (H σ) (Sum.inr (j,v,u))-
        (FiniteLaw.pi μ).expectation (fun τ=>typedMarkedPotentialLoad w (Q τ) (H τ) (Sum.inr (j,v,u)))|)≤
      2*Real.exp (-2*t^2/(Bloc^2*(((m:ℝ)+1)^4*B/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B))) := by
  have hn0 : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have hr0 : (0:ℝ)<(m:ℝ)+1 := by positivity
  have hh := resourcePatternLoad_supported_tail μ typedMarkedOccurrenceResources w (fun W=>(hw W).1)
    (fun _ _=>true) S (fun σ=>typedMarkedResourceState (Q σ) (H σ)) hs Bloc hBloc hread haffect (Sum.inr (j,v,u))
    (2*((m:ℝ)+1)) (((m:ℝ)+1)^2*B) (((m:ℝ)+1)^4*B/Fintype.card V) (by positivity) (by positivity) (by positivity)
    (by
      intro W _
      have hc := Finset.card_le_card (Finset.sdiff_subset : typedMarkedOccurrenceResources W\{(Sum.inr (j,v,u))}⊆typedMarkedOccurrenceResources W)
      exact_mod_cast hc.trans (typedMarkedOccurrenceResources_card W))
    (typedMarkedSpoke_resource_load_bound hn w B hB (fun W=>(hw W).2) j v u)
    (typedMarkedSpoke_omitted_pair_bound hm hn w B hB hw j v u) t ht
  simpa only [← typedMarkedPotentialLoad_eq_pattern] using hh

theorem typedMarkedSpoke_supported_common_event
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
    1-(Fintype.card (Bool×V×U):ℝ)*
      (2*Real.exp (-2*t^2/(Bloc^2*(((m:ℝ)+1)^4*B/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B))))≤
      (FiniteLaw.pi μ).probability (fun σ=>∀ root : Bool×V×U,
        |typedMarkedPotentialLoad w (Q σ) (H σ) (Sum.inr root)-
          (FiniteLaw.pi μ).expectation (fun τ=>typedMarkedPotentialLoad w (Q τ) (H τ) (Sum.inr root))|<t) := by
  have hh := finiteLaw_common_event_lower (FiniteLaw.pi μ) Finset.univ
    (fun (root : Bool×V×U) σ=>t≤|typedMarkedPotentialLoad w (Q σ) (H σ) (Sum.inr root)-
      (FiniteLaw.pi μ).expectation (fun τ=>typedMarkedPotentialLoad w (Q τ) (H τ) (Sum.inr root))|)
    (fun _=>2*Real.exp (-2*t^2/(Bloc^2*(((m:ℝ)+1)^4*B/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B))))
    (fun root _=>typedMarkedSpoke_supported_tail hm hn w B hB hw
      μ Q H S hs Bloc hBloc hBp hread haffect root.1 root.2.1 root.2.2 t ht)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies,not_le] using hh

end Oberwolfach
