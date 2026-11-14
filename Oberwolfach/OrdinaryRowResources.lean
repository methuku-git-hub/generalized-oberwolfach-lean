module

public import Oberwolfach.RawOrdinaryPatternSampling

@[expose] public section

/-! The physical resources for one ordinary common-neighbour count.
A physical edge contributes to at most its two endpoint positions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryRowResources (S:Finset V) (J:Finset U) (z:V):Finset (Sym2 V⊕(V×U)):=
  (S.image (fun x=>Sum.inl s(x,z)))∪(J.image (fun u=>Sum.inr (z,u)))

theorem ordinaryRowResources_rim (S:Finset V) (J:Finset U) (z:V) (e:Sym2 V):
    Sum.inl e∈ordinaryRowResources S J z ↔ ∃ x∈S,s(x,z)=e:=by
  simp [ordinaryRowResources]

theorem ordinaryRowResources_spoke (S:Finset V) (J:Finset U) (z:V) (a:V×U):
    Sum.inr a∈ordinaryRowResources S J z ↔ a.1=z ∧ a.2∈J:=by
  rcases a with ⟨a,u⟩
  simp [ordinaryRowResources,eq_comm,and_comm]

theorem ordinaryRowResources_card (S:Finset V) (J:Finset U) (z:V):
    (ordinaryRowResources S J z).card≤S.card+J.card:=
  (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)

theorem ordinaryRowResources_incidence (S:Finset V) (J:Finset U) (C:Finset V)
    (e:Sym2 V⊕(V×U)):(C.filter (fun z=>e∈ordinaryRowResources S J z)).card≤2:=by
  cases e with
  | inl e=>
    induction e using Sym2.ind with
    | _ a b=>
      have hsub:C.filter (fun z=>Sum.inl s(a,b)∈ordinaryRowResources S J z)⊆{a,b}:=by
        intro z hz
        obtain ⟨x,hx,he⟩:=(ordinaryRowResources_rim S J z s(a,b)).mp (Finset.mem_filter.mp hz).2
        have hh:=Sym2.eq_iff.mp he
        simp only [Finset.mem_insert,Finset.mem_singleton]
        rcases hh with h|h <;> tauto
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
  | inr a=>
    have hsub:C.filter (fun z=>Sum.inr a∈ordinaryRowResources S J z)⊆{a.1}:=by
      intro z hz
      exact Finset.mem_singleton.mpr ((ordinaryRowResources_spoke S J z a).mp (Finset.mem_filter.mp hz).2).1.symm
    have hh:=Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hh
    omega

theorem ordinaryRowResources_load (S:Finset V) (J:Finset U) (C:Finset V) (e:Sym2 V⊕(V×U)):
    (∑ z:C,if e∈ordinaryRowResources S J z.val then (1:ℝ) else 0)≤2:=by
  rw [Finset.sum_coe_sort C (fun z:V=>if e∈ordinaryRowResources S J z then (1:ℝ) else 0)]
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
  exact_mod_cast ordinaryRowResources_incidence S J C e

theorem ordinaryRowResources_disjoint (π:Equiv.Perm V) (d:ℕ) (S:Finset V) (J:Finset U) (z:V)
    (a b:Sym2 V⊕(V×U)) (ha:a∈ordinaryRowResources S J z)
    (hb:b∈ordinaryRowResources S J z) (hne:a≠b):
    Disjoint (rawWheelResourceCoordinates π d a) (rawWheelResourceCoordinates π d b):=by
  apply rawWheelResourceCoordinates_disjoint π d a b hne
  intro v u w t he hf
  subst a;subst b
  have hz:=(ordinaryRowResources_spoke S J z (v,u)).mp ha
  have hz':=(ordinaryRowResources_spoke S J z (w,t)).mp hb
  left
  intro hut
  apply hne
  exact congrArg Sum.inr (Prod.ext (hz.1.trans hz'.1.symm) hut)

end Oberwolfach
