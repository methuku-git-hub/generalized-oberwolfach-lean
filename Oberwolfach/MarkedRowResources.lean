module

public import Oberwolfach.RawMarkedPatternSampling

@[expose] public section

/-! The resources in a marked row count. A rim request specifies its
ordinary/marked type, incoming/outgoing direction, and fixed root. A spoke
request specifies its type and hub. No root is required to lie in the row set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

def markedRowRim (a : Bool×Bool×V) (z : V) : (V×V)⊕(V×V) :=
  let xy := if a.2.1 then (z,a.2.2) else (a.2.2,z)
  if a.1 then Sum.inr xy else Sum.inl xy

def markedRowResources (S : Finset (Bool×Bool×V)) (J : Finset (Bool×U))
    (z : V) : Finset (MarkedResource V U) :=
  (S.image (fun a=>Sum.inl (markedRowRim a z))) ∪
    (J.image (fun a=>Sum.inr (a.1,z,a.2)))

theorem markedRowResources_rim (S : Finset (Bool×Bool×V)) (J : Finset (Bool×U))
    (z : V) (e : (V×V)⊕(V×V)) :
    Sum.inl e∈markedRowResources S J z ↔ ∃ a∈S,markedRowRim a z=e := by
  simp [markedRowResources]

theorem markedRowResources_spoke (S : Finset (Bool×Bool×V)) (J : Finset (Bool×U))
    (z : V) (a : Bool×V×U) :
    Sum.inr a∈markedRowResources S J z ↔ a.2.1=z ∧ (a.1,a.2.2)∈J := by
  constructor
  · intro ha
    rcases Finset.mem_union.mp ha with ha|ha
    · obtain ⟨x,hx,he⟩ := Finset.mem_image.mp ha
      cases he
    · obtain ⟨x,hx,he⟩ := Finset.mem_image.mp ha
      have he' := Sum.inr.inj he
      have hz := congrArg (fun y : Bool×V×U=>y.2.1) he'
      have hx' := congrArg (fun y : Bool×V×U=>(y.1,y.2.2)) he'
      exact ⟨hz.symm,hx' ▸ hx⟩
  · intro ha
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨(a.1,a.2.2),ha.2,?_⟩
    apply congrArg Sum.inr
    exact Prod.ext rfl (Prod.ext ha.1.symm rfl)

theorem markedRowResources_card (S : Finset (Bool×Bool×V)) (J : Finset (Bool×U)) (z : V) :
    (markedRowResources S J z).card≤S.card+J.card := by
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)

theorem markedRowRim_variable (a : Bool×Bool×V) (z : V) :
    (Sum.elim Prod.fst Prod.fst (markedRowRim a z)=z) ∨
      (Sum.elim Prod.snd Prod.snd (markedRowRim a z)=z) := by
  obtain ⟨b,c,x⟩ := a
  cases b <;> cases c <;> simp [markedRowRim]

theorem markedRowResources_incidence (S : Finset (Bool×Bool×V)) (J : Finset (Bool×U))
    (C : Finset V) (e : MarkedResource V U) :
    (C.filter (fun z=>e∈markedRowResources S J z)).card≤2 := by
  cases e with
  | inl e=>
    have hsub : C.filter (fun z=>Sum.inl e∈markedRowResources S J z)⊆
        {Sum.elim Prod.fst Prod.fst e,Sum.elim Prod.snd Prod.snd e} := by
      intro z hz
      obtain ⟨a,ha,he⟩ := (markedRowResources_rim S J z e).mp (Finset.mem_filter.mp hz).2
      have hh := markedRowRim_variable a z
      rw [he] at hh
      simpa only [Finset.mem_insert,Finset.mem_singleton,eq_comm] using hh
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  | inr a=>
    have hsub : C.filter (fun z=>Sum.inr a∈markedRowResources S J z)⊆{a.2.1} := by
      intro z hz
      exact Finset.mem_singleton.mpr ((markedRowResources_spoke S J z a).mp (Finset.mem_filter.mp hz).2).1.symm
    have hh := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hh
    omega

theorem markedRowResources_load (S : Finset (Bool×Bool×V)) (J : Finset (Bool×U))
    (C : Finset V) (e : MarkedResource V U) :
    (∑ z : C,if e∈markedRowResources S J z.val then (1:ℝ) else 0)≤2 := by
  rw [Finset.sum_coe_sort C (fun z : V=>if e∈markedRowResources S J z then (1:ℝ) else 0)]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
  exact_mod_cast markedRowResources_incidence S J C e

theorem markedRowResources_disjoint (π : Equiv.Perm V) (d : ℕ)
    (S : Finset (Bool×Bool×V)) (J : Finset (Bool×U)) (z : V)
    (hphys : Set.InjOn (fun a=>markedPairPhysical π (markedRowRim a z)) S)
    (hJ : Set.InjOn (fun a : Bool×U=>a.2) J)
    (a b : MarkedResource V U) (ha : a∈markedRowResources S J z)
    (hb : b∈markedRowResources S J z) (hne : a≠b) :
    Disjoint (rawMarkedResourceCoordinates π d a) (rawMarkedResourceCoordinates π d b) := by
  apply rawMarkedResourceCoordinates_disjoint π d a b
  cases a with
  | inl a=>cases b with
    | inl b=>
      obtain ⟨x,hx,hxa⟩ := (markedRowResources_rim S J z a).mp ha
      obtain ⟨y,hy,hyb⟩ := (markedRowResources_rim S J z b).mp hb
      intro he
      have hxy := hphys hx hy (by simpa only [hxa,hyb] using he)
      apply hne
      exact congrArg Sum.inl (hxa.symm.trans (hxy ▸ hyb))
    | inr b=>trivial
  | inr a=>cases b with
    | inl b=>trivial
    | inr b=>
      have ha' := (markedRowResources_spoke S J z a).mp ha
      have hb' := (markedRowResources_spoke S J z b).mp hb
      left
      intro he
      have hpair := hJ ha'.2 hb'.2 he
      apply hne
      apply congrArg Sum.inr
      exact Prod.ext (congrArg (fun x : Bool×U=>x.1) hpair) (Prod.ext (ha'.1.trans hb'.1.symm) he)

end Oberwolfach
