module

public import Oberwolfach.OrdinaryWheelLoads
public import Oberwolfach.WeightedProducts

@[expose] public section

/-! Potential ordinary-wheel loads on a fixed parent family. The physical
root edge is erased from every tested edge set, whether or not it is present
in the current host. Candidate wheels and their coefficients are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {P F : SimpleGraph V} {Hbase : V → U → Prop} {r : ℕ}

def ordinaryWheelResources (W : OrdinaryWheel P F Hbase r) : Finset (Sym2 V⊕(V×U)) :=
  (ordinaryWheelRim W).edgeFinset.image Sum.inl ∪
    (ordinaryWheelRim W).support.toFinset.image (fun v=>Sum.inr (v,ordinaryWheelHub W))

theorem ordinaryWheelResources_rim (W : OrdinaryWheel P F Hbase r) (e : Sym2 V) :
    Sum.inl e∈ordinaryWheelResources W ↔ e∈(ordinaryWheelRim W).edgeSet := by
  classical
  simp [ordinaryWheelResources]

theorem ordinaryWheelResources_spoke (W : OrdinaryWheel P F Hbase r) (v : V) (u : U) :
    Sum.inr (v,u)∈ordinaryWheelResources W ↔ ordinaryWheelHub W=u ∧ v∈(ordinaryWheelRim W).support := by
  classical
  simp only [ordinaryWheelResources,Finset.mem_union,Finset.mem_image,Sum.inl_ne_inr,false_and,and_false,exists_false,false_or,
    Sum.inr.injEq,Prod.mk.injEq,Set.mem_toFinset]
  constructor
  · rintro ⟨x,hx,hxv,hu⟩
    exact ⟨hu,hxv ▸ hx⟩
  · rintro ⟨hu,hv⟩
    exact ⟨v,hv,rfl,hu⟩

def ordinaryResourceState (Q : SimpleGraph V) (H : V → U → Prop) : Sym2 V⊕(V×U) → Bool :=
  Sum.elim (fun e=>decide (e∈Q.edgeSet)) (fun vu=>decide (H vu.1 vu.2))

def ordinaryPotentialLoad (w : OrdinaryWheel P F Hbase r → ℝ)
    (root : Sym2 V⊕(V×U)) (Q : SimpleGraph V) (H : V → U → Prop) : ℝ :=
  ∑ W, (if root∈ordinaryWheelResources W then w W else 0)*
    patternValue (ordinaryWheelResources W\{root}) (fun _=>true) (ordinaryResourceState Q H)

theorem ordinaryPotentialLoad_stability
    (w : OrdinaryWheel P F Hbase r → ℝ) (hw : ∀ W,0≤w W)
    (root : Sym2 V⊕(V×U)) (Q Q' : SimpleGraph V) (H H' : V → U → Prop)
    (D : Finset (Sym2 V⊕(V×U)))
    (hD : ∀ e,e∉D → ordinaryResourceState Q H e=ordinaryResourceState Q' H' e) :
    |ordinaryPotentialLoad w root Q' H'-ordinaryPotentialLoad w root Q H|≤
      ∑ e∈D,∑ W,if root∈ordinaryWheelResources W ∧ e∈ordinaryWheelResources W ∧ e≠root then w W else 0 := by
  classical
  have hh := omitted_root_stability Finset.univ ordinaryWheelResources {root} D (fun _ _=>true)
    (fun W=>if root∈ordinaryWheelResources W then w W else 0)
    (ordinaryResourceState Q H) (ordinaryResourceState Q' H')
    (by intro W _;split_ifs;exact hw W;norm_num)
    (by intro W _ e _ _ he;exact hD e he)
  change |ordinaryPotentialLoad w root Q' H'-ordinaryPotentialLoad w root Q H|≤_ at hh
  apply hh.trans_eq
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro W _
  simp only [Finset.mem_sdiff,Finset.mem_singleton]
  split_ifs <;> simp_all

theorem ordinaryPotentialLoad_present
    (w : OrdinaryWheel P F Hbase r → ℝ) (root : Sym2 V⊕(V×U))
    (Q : SimpleGraph V) (H : V → U → Prop) (hr : ordinaryResourceState Q H root=true) :
    ordinaryPotentialLoad w root Q H=
      ∑ W,if root∈ordinaryWheelResources W ∧
        (∀ e∈ordinaryWheelResources W,ordinaryResourceState Q H e=true) then w W else 0 := by
  unfold ordinaryPotentialLoad
  apply Finset.sum_congr rfl
  intro W _
  rw [patternValue_indicator]
  have he : (∀ e∈ordinaryWheelResources W\{root},ordinaryResourceState Q H e=true) ↔
      (∀ e∈ordinaryWheelResources W,ordinaryResourceState Q H e=true) := by
    constructor
    · intro h e he
      by_cases her : e=root
      · simpa only [her] using hr
      · exact h e (Finset.mem_sdiff.mpr ⟨he,by simpa only [Finset.mem_singleton] using her⟩)
    · intro h e he;exact h e (Finset.mem_sdiff.mp he).1
  simp only [he]
  split_ifs <;> simp_all

end Oberwolfach
