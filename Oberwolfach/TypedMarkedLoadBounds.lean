module

public import Oberwolfach.TypedMarkedPairCosts
public import Oberwolfach.ResourcePatternConcentration

@[expose] public section

/-! Uniform load and pair bounds for the fixed typed parent-wheel universe.
No injectivity of its physical representation map is assumed. -/
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

theorem typedMarkedOccurrenceResources_card
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :
    (typedMarkedOccurrenceResources W).card≤2*(m+1) := by
  have he : Finset.univ.filter (fun e=>CanonicalMarkedArcMem W.1 e)=
      Finset.univ.image (markedCycleTypedEdge tail head ktail khead m π b W.1) := by
    ext e;simp [CanonicalMarkedArcMem]
  unfold typedMarkedOccurrenceResources
  have h₁ := Finset.card_union_le
    ((Finset.univ.filter (fun e=>CanonicalMarkedArcMem W.1 e)).image (Sum.inl (β:=Bool×V×U)))
    (Finset.univ.image (fun i=>Sum.inr (α:=E⊕K) (decide (i=0),W.1.val i,W.2.val)))
  have h₂ := Finset.card_image_le (s:=Finset.univ.filter (fun e=>CanonicalMarkedArcMem W.1 e))
    (f:=Sum.inl (β:=Bool×V×U))
  rw [he] at h₂
  have h₃ := Finset.card_image_le (s:=(Finset.univ : Finset (Fin (m+1))))
    (f:=markedCycleTypedEdge tail head ktail khead m π b W.1)
  have h₄ := Finset.card_image_le (s:=(Finset.univ : Finset (Fin (m+1))))
    (f:=fun i=>Sum.inr (α:=E⊕K) (decide (i=0),W.1.val i,W.2.val))
  simp only [Finset.card_univ,Fintype.card_fin] at h₃ h₄
  rw [he] at h₁ ⊢
  omega

theorem typedMarkedOccurrenceResources_load_bound
    (hm : 1≤m) (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (e : (E⊕K)⊕(Bool×V×U)) :
    (∑ W,if e∈typedMarkedOccurrenceResources W then w W else 0)≤((m:ℝ)+1)^2*B := by
  cases e with
  | inl e =>
    simp only [typedMarkedOccurrenceResources_rim]
    by_cases hex : ∃ W : MarkedWheel tail head ktail khead m π b H₀ Hₖ,CanonicalMarkedArcMem W.1 e
    · obtain ⟨W,hW⟩ := hex
      have hne := canonicalMarkedArc_nonloop hm W.1 e hW
      have hc : ({Sum.elim tail ktail e,Sum.elim head khead e}:Finset V).card=2 := by simp [hne]
      have hh := marked_wheel_free_hub_event hn hu w B hB (fun W=>(hw W).2)
        {Sum.elim tail ktail e,Sum.elim head khead e} (by omega) (by omega)
        (fun W=>CanonicalMarkedArcMem W.1 e) (by
          intro Z hZ v hv
          have h := canonicalMarkedArc_endpoints_present Z.1 e hZ
          simp only [Finset.mem_insert,Finset.mem_singleton] at hv
          rcases hv with rfl|rfl
          · exact h.1
          · exact h.2)
      simpa only [hc,show 2-2=0 from rfl,pow_zero,div_one] using hh
    · have hf : ∀ W : MarkedWheel tail head ktail khead m π b H₀ Hₖ,¬CanonicalMarkedArcMem W.1 e := by
        simpa only [not_exists] using hex
      simp only [hf,ite_false,Finset.sum_const_zero];positivity
  | inr jvu =>
    obtain ⟨j,v,u⟩ := jvu
    have hh := marked_wheel_fixed_hub_event hn w B hB (fun W=>(hw W).2)
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

theorem typedMarkedOmittedPair_uniform_bound
    (hm : 3≤m) (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (e f : (E⊕K)⊕(Bool×V×U)) :
    resourceOmittedPairWeight typedMarkedOccurrenceResources w e f≤((m:ℝ)+1)^4*B/Fintype.card V := by
  have hnR : (1:ℝ)≤Fintype.card V := by exact_mod_cast (show 1≤Fintype.card V by omega)
  have hscale : ((m:ℝ)+1)^4*B/(Fintype.card V:ℝ)^2≤((m:ℝ)+1)^4*B/Fintype.card V := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      apply (typedMarkedPair_rim_rim hm hn hu w B hB hw e f).trans
      split_ifs <;> first | exact le_refl _ | exact hscale
    | inr f =>
      apply (typedMarkedPair_rim_spoke hm hn w B hB hw e f.1 f.2.1 f.2.2).trans
      split_ifs <;> first | exact le_refl _ | exact hscale
  | inr e =>
    cases f with
    | inl f =>
      apply (typedMarkedPair_spoke_rim hm hn w B hB hw f e.1 e.2.1 e.2.2).trans
      split_ifs <;> first | exact le_refl _ | exact hscale
    | inr f =>
      apply (typedMarkedPair_spoke_spoke hm hn w B hB hw e.1 f.1 e.2.1 f.2.1 e.2.2 f.2.2).trans
      split_ifs <;> first | exact le_refl _ | positivity

def typedMarkedResourceState (R : E⊕K → Prop) (H : Bool→V→U→Prop) :
    (E⊕K)⊕(Bool×V×U) → Bool :=
  fun e=>decide (Sum.elim R (fun jvu=>H jvu.1 jvu.2.1 jvu.2.2) e)

theorem typedMarkedPotentialLoad_eq_pattern
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ)
    (R : E⊕K → Prop) (H : Bool→V→U→Prop) (e : (E⊕K)⊕(Bool×V×U)) :
    typedMarkedPotentialLoad w R H e=
      resourcePatternLoad typedMarkedOccurrenceResources w (fun _ _=>true) e (typedMarkedResourceState R H) := by
  unfold typedMarkedPotentialLoad resourceRootOmittedLoad resourcePatternLoad
  apply Finset.sum_congr rfl
  intro W _
  rw [patternValue_indicator]
  simp only [typedMarkedResourceState,decide_eq_true_eq,Finset.mem_sdiff,Finset.mem_singleton]
  have heq : (∀ f,f∈typedMarkedOccurrenceResources W ∧ f≠e →
      Sum.elim R (fun jvu=>H jvu.1 jvu.2.1 jvu.2.2) f) ↔
      (∀ f∈typedMarkedOccurrenceResources W,f≠e → Sum.elim R (fun jvu=>H jvu.1 jvu.2.1 jvu.2.2) f) := by
    aesop
  simp only [heq]
  split_ifs <;> simp_all

end Oberwolfach
