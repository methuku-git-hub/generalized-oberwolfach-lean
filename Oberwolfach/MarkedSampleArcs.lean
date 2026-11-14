module

public import Oberwolfach.MarkedPhysicalCuts
public import Oberwolfach.MarkedPhysicalCycleProperties

@[expose] public section

/-! The actual sampled typed arcs have an injective physical map. This
uses the one state assigned to each unordered physical edge; it does not
assert injectivity for the full universe of potential ordinary/marked arcs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V : Type*} [LinearOrder V]

theorem orientationBit_ne_swap (x y : V) (hxy : x≠y) : orientationBit x y≠orientationBit y x := by
  rcases lt_or_gt_of_ne hxy with h|h
  · simp [orientationBit,h,not_lt_of_gt h]
  · simp [orientationBit,h,not_lt_of_gt h]

theorem markedPhysicalRim_eq_one_iff (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (σ : Sym2 V→Option (Bool×Bool)) (a : Bool) (x y : V) :
    markedPhysicalRim P π b σ a x y=1 ↔
      ¬PermutationClose π b x y ∧ P.Adj x (if a then π y else y) ∧
        σ s(x,if a then π y else y)=some (a,orientationBit x (if a then π y else y)) := by
  unfold markedPhysicalRim permutationSeparatedMatrix markedPhysicalOrientation
  split_ifs <;> simp_all

theorem markedPhysicalRim_physical_unique (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (σ : Sym2 V→Option (Bool×Bool)) (a a' : Bool) (x y x' y' : V)
    (h : markedPhysicalRim P π b σ a x y=1) (h' : markedPhysicalRim P π b σ a' x' y'=1)
    (he : s(x,if a then π y else y)=s(x',if a' then π y' else y')) :
    a=a' ∧ x=x' ∧ y=y' := by
  have hh := (markedPhysicalRim_eq_one_iff P π b σ a x y).mp h
  have hh' := (markedPhysicalRim_eq_one_iff P π b σ a' x' y').mp h'
  have hs := hh.2.2
  rw [he,hh'.2.2] at hs
  have hstates := Prod.mk.inj (Option.some.inj hs)
  have ha : a=a' := hstates.1.symm
  subst a'
  rcases Sym2.eq_iff.mp he with ⟨hxx,hyy⟩|⟨hxy,hyx⟩
  · refine ⟨rfl,hxx,?_⟩
    cases a
    · exact hyy
    · exact π.injective hyy
  · have hbits : orientationBit x (if a then π y else y)=
        orientationBit (if a then π y else y) x := by
      simpa only [← hxy,← hyx] using hstates.2.symm
    exact ((orientationBit_ne_swap x _ hh.2.1.ne) hbits).elim

abbrev MarkedSampleArc (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (σ : Sym2 V→Option (Bool×Bool)) (a : Bool) :=
  {e : V×V // markedPhysicalRim P π b σ a e.1 e.2=1}

theorem markedSampleArc_physical_injective (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (σ : Sym2 V→Option (Bool×Bool)) :
    Function.Injective (markedPhysicalEdge
      (fun e : MarkedSampleArc P π b σ false=>e.val.1)
      (fun e : MarkedSampleArc P π b σ false=>e.val.2)
      (fun e : MarkedSampleArc P π b σ true=>e.val.1)
      (fun e : MarkedSampleArc P π b σ true=>e.val.2) π) := by
  have hpair (x y x' y' : V) (h : ({x,y}:Finset V)={x',y'}) : s(x,y)=s(x',y') := by
    apply Sym2.eq_iff.mpr
    apply Set.pair_eq_pair_iff.mp
    simpa only [Finset.coe_pair] using congrArg (fun S : Finset V=>(S:Set V)) h
  intro e f he
  cases e with
  | inl e=>cases f with
    | inl f=>
      have hh := markedPhysicalRim_physical_unique P π b σ false false e.val.1 e.val.2 f.val.1 f.val.2
        e.property f.property (hpair _ _ _ _ he)
      exact congrArg Sum.inl (Subtype.ext (Prod.ext hh.2.1 hh.2.2))
    | inr f=>
      have hh := markedPhysicalRim_physical_unique P π b σ false true e.val.1 e.val.2 f.val.1 f.val.2
        e.property f.property (hpair _ _ _ _ he)
      cases hh.1
  | inr e=>cases f with
    | inl f=>
      have hh := markedPhysicalRim_physical_unique P π b σ true false e.val.1 e.val.2 f.val.1 f.val.2
        e.property f.property (hpair _ _ _ _ he)
      cases hh.1
    | inr f=>
      have hh := markedPhysicalRim_physical_unique P π b σ true true e.val.1 e.val.2 f.val.1 f.val.2
        e.property f.property (hpair _ _ _ _ he)
      exact congrArg Sum.inr (Subtype.ext (Prod.ext hh.2.1 hh.2.2))

end Oberwolfach
