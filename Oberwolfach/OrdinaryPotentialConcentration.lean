module

public import Oberwolfach.ResourcePatternConcentration
public import Oberwolfach.OrdinaryWheelCodegrees
public import Oberwolfach.OrdinaryWheelResources
public import Oberwolfach.OrdinaryPotentialDegreeStability

@[expose] public section

/-! Sampling of the actual ordinary-wheel family with its fixed coefficients.
The resource-state functions may depend locally on shared primitive trials;
no independence of the spoke states is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
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

theorem ordinary_wheel_rim_load_bound (x y : V) : ordinaryRimLoad w x y≤(r:ℝ)^2*B := by
  by_cases hxy : x=y
  · subst y;simp [ordinaryRimLoad];positivity
  have hc : ({x,y}:Finset V).card=2 := by simp [hxy]
  have hh := ordinary_wheel_free_hub_event P F Hbase r hr hn w B hB hw hu {x,y}
    (by rw [hc]) (fun W=>(ordinaryWheelRim W).Adj x y)
    (by
      intro W h z hz
      simp only [Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] at hz
      rcases hz with rfl|rfl
      · exact h.mem_support_left
      · exact h.mem_support_right)
  simpa only [ordinaryRimLoad,hc,show 2-2=0 from rfl,pow_zero,div_one] using hh

theorem ordinary_wheel_spoke_load_bound (v : V) (u : U) : ordinarySpokeLoad w v u≤(r:ℝ)^2*B := by
  have hn0 : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have hrow (y : V) :
      (∑ W,if (ordinaryWheelRim W).Adj v y ∧ ordinaryWheelHub W=u then w W else 0)≤
        (r:ℝ)^2*B/Fintype.card V := by
    by_cases hvy : v=y
    · subst y;simp only [SimpleGraph.irrefl,false_and,ite_false,Finset.sum_const_zero];positivity
    have hh := ordinary_wheel_rim_spoke_pair P F Hbase r hr hn w B hB hw v y hvy v u
    convert hh using 1
    apply Finset.sum_congr rfl
    intro W _
    have he : ((ordinaryWheelRim W).Adj v y ∧ ordinaryWheelHub W=u ∧ v∈(ordinaryWheelRim W).support)↔
        ((ordinaryWheelRim W).Adj v y ∧ ordinaryWheelHub W=u) :=
      ⟨fun h=>⟨h.1,h.2.1⟩,fun h=>⟨h.1,h.2,h.1.mem_support_left⟩⟩
    simp only [he]
  have heq : (∑ y,∑ W,if (ordinaryWheelRim W).Adj v y ∧ ordinaryWheelHub W=u then w W else 0)=
      2*ordinarySpokeLoad w v u := by
    rw [Finset.sum_comm]
    unfold ordinarySpokeLoad
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro W _
    by_cases huW : ordinaryWheelHub W=u
    · simp only [huW,and_true,true_and]
      exact embedded_cycle_weighted_row W.val.1.val.property v (w W)
    · simp only [huW,and_false,false_and,ite_false,Finset.sum_const_zero,mul_zero]
  have hh := Finset.sum_le_sum (fun y (_ : y∈Finset.univ)=>hrow y)
  rw [heq] at hh
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  have he : (Fintype.card V:ℝ)*((r:ℝ)^2*B/Fintype.card V)=(r:ℝ)^2*B := by field_simp
  rw [he] at hh
  have hp : 0≤(r:ℝ)^2*B := by positivity
  linarith

theorem ordinary_wheel_resource_load_bound (e : Sym2 V⊕(V×U)) :
    (∑ W,if e∈ordinaryWheelResources W then w W else 0)≤(r:ℝ)^2*B := by
  cases e with
  | inl e =>
    induction e using Sym2.ind with
    | _ x y =>
      rw [ordinaryWheelResources_load_rim]
      exact ordinary_wheel_rim_load_bound P F Hbase r hr hn hu w B hB hw x y
  | inr vu =>
    rw [ordinaryWheelResources_load_spoke]
    exact ordinary_wheel_spoke_load_bound P F Hbase r hr hn hu w B hB hw vu.1 vu.2

theorem ordinary_wheel_omitted_pair_bound (e f : Sym2 V⊕(V×U)) :
    resourceOmittedPairWeight ordinaryWheelResources w e f≤(r:ℝ)^4*B/Fintype.card V := by
  by_cases hef : e=f
  · subst f;simp [resourceOmittedPairWeight];positivity
  have hh := ordinary_wheel_physical_pair_load P F Hbase r hr hn hu w B hB hw e f hef
  simpa [resourceOmittedPairWeight,Ne.symm hef] using hh

omit hr hn hu hB hw in
theorem ordinaryPotentialLoad_eq_pattern (Q : SimpleGraph V) (H : V → U → Prop)
    (e : Sym2 V⊕(V×U)) :
    ordinaryPotentialLoad w e Q H=
      resourcePatternLoad ordinaryWheelResources w (fun _ _=>true) e (ordinaryResourceState Q H) := rfl

theorem ordinaryPotentialLoad_supported_tail
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
      |ordinaryPotentialLoad w root (Q σ) (H σ)-
        (FiniteLaw.pi μ).expectation (fun τ=>ordinaryPotentialLoad w root (Q τ) (H τ))|)≤
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


theorem ordinaryPotentialLoad_supported_common_event
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
        |ordinaryPotentialLoad w root (Q σ) (H σ)-
          (FiniteLaw.pi μ).expectation (fun τ=>ordinaryPotentialLoad w root (Q τ) (H τ))|<t) := by
  have hh := finiteLaw_common_event_lower (FiniteLaw.pi μ) Finset.univ
    (fun root σ=>t≤|ordinaryPotentialLoad w root (Q σ) (H σ)-
      (FiniteLaw.pi μ).expectation (fun τ=>ordinaryPotentialLoad w root (Q τ) (H τ))|)
    (fun _=>2*Real.exp (-2*t^2/(Bloc^2*((r:ℝ)^4*B/Fintype.card V)*(2*r)*((r:ℝ)^2*B))))
    (fun root _=>ordinaryPotentialLoad_supported_tail P F Hbase r hr hn hu w B hB hw
      μ Q H S hs Bloc hBloc hBp hread haffect root t ht)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies,not_le] using hh

/-- One sampled event controls every later degree-bounded modification.
The realised deletion/addition cost is not multiplied by a sampling density. -/
theorem ordinaryPotentialLoad_adaptive_common_event
    {E : Type*} [Fintype E] [DecidableEq E]
    {Base : E → Type*} [∀ e,Fintype (Base e)]
    (μ : ∀ e,FiniteLaw (Base e))
    (Q : (∀ e,Base e) → SimpleGraph V) (H : (∀ e,Base e) → V → U → Prop)
    (S : Sym2 V⊕(V×U) → Finset E)
    (hs : ∀ a σ τ,(∀ e∈S a,σ e=τ e) → ordinaryResourceState (Q σ) (H σ) a=ordinaryResourceState (Q τ) (H τ) a)
    (Bloc : ℝ) (hBloc : 0<Bloc) (hBp : 0<B)
    (hread : ∀ a,((S a).card:ℝ)≤Bloc)
    (haffect : ∀ e,((Finset.univ.filter (fun a=>e∈S a)).card:ℝ)≤Bloc)
    (t d : ℝ) (ht : 0<t) (hd : 0≤d) :
    1-(Fintype.card (Sym2 V⊕(V×U)):ℝ)*
      (2*Real.exp (-2*t^2/(Bloc^2*((r:ℝ)^4*B/Fintype.card V)*(2*r)*((r:ℝ)^2*B))))≤
      (FiniteLaw.pi μ).probability (fun σ=>∀ (Q' : SimpleGraph V) (H' : V → U → Prop),
        (∀ x,(∑ y,bipAdj (fun x y=>¬((Q σ).Adj x y↔Q'.Adj x y)) x y)≤d) →
        (∀ x,(∑ u,bipAdj (fun x u=>¬(H σ x u↔H' x u)) x u)≤d) →
        (∀ u,(∑ x,bipAdj (fun x u=>¬(H σ x u↔H' x u)) x u)≤d) →
        (∀ x y,x≠y → |ordinaryPotentialLoad w (Sum.inl s(x,y)) Q' H'-
          (FiniteLaw.pi μ).expectation (fun τ=>ordinaryPotentialLoad w (Sum.inl s(x,y)) (Q τ) (H τ))|≤
            t+8*(r:ℝ)^4*B*d/Fintype.card V) ∧
        (∀ v u,|ordinaryPotentialLoad w (Sum.inr (v,u)) Q' H'-
          (FiniteLaw.pi μ).expectation (fun τ=>ordinaryPotentialLoad w (Sum.inr (v,u)) (Q τ) (H τ))|≤
            t+4*(r:ℝ)^4*B*d/Fintype.card V)) := by
  apply (ordinaryPotentialLoad_supported_common_event P F Hbase r hr hn hu w B hB hw
    μ Q H S hs Bloc hBloc hBp hread haffect t ht).trans
  apply finiteLaw_probability_mono
  intro σ he Q' H' hQ hHo hHi
  constructor
  · intro x y hxy
    have hs' := ordinaryPotentialLoad_rim_degree_stability P F Hbase r hr hn hu w B hB hw
      (Q σ) Q' (H σ) H' d hd hQ hHo hHi x y hxy
    calc
      _ ≤ |ordinaryPotentialLoad w (Sum.inl s(x,y)) Q' H'-ordinaryPotentialLoad w (Sum.inl s(x,y)) (Q σ) (H σ)|+
          |ordinaryPotentialLoad w (Sum.inl s(x,y)) (Q σ) (H σ)-
            (FiniteLaw.pi μ).expectation (fun τ=>ordinaryPotentialLoad w (Sum.inl s(x,y)) (Q τ) (H τ))| :=
        abs_sub_le _ _ _
      _ ≤ 8*(r:ℝ)^4*B*d/Fintype.card V+t := add_le_add hs' (he _).le
      _ = _ := by ring
  · intro v u
    have hs' := ordinaryPotentialLoad_spoke_degree_stability P F Hbase r hr hn hu w B hB hw
      (Q σ) Q' (H σ) H' d hd hQ hHo hHi v u
    calc
      _ ≤ |ordinaryPotentialLoad w (Sum.inr (v,u)) Q' H'-ordinaryPotentialLoad w (Sum.inr (v,u)) (Q σ) (H σ)|+
          |ordinaryPotentialLoad w (Sum.inr (v,u)) (Q σ) (H σ)-
            (FiniteLaw.pi μ).expectation (fun τ=>ordinaryPotentialLoad w (Sum.inr (v,u)) (Q τ) (H τ))| :=
        abs_sub_le _ _ _
      _ ≤ 4*(r:ℝ)^4*B*d/Fintype.card V+t := add_le_add hs' (he _).le
      _ = _ := by ring

end Oberwolfach
