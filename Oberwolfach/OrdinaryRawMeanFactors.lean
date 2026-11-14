module

public import Oberwolfach.OrdinaryRawIntervalSampling

@[expose] public section

/-! The root omission leaves exactly r-1 rim factors and r spoke factors,
or r rim factors and r-1 spoke factors. These are unconditional means. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {P F : SimpleGraph V} {Hbase : V → U → Prop} {r : ℕ}

theorem ordinaryWheelResources_constant_product (W : OrdinaryWheel P F Hbase r) (pR pH : ℝ) :
    (∏ e∈ordinaryWheelResources W,Sum.elim (fun _=>pR) (fun _=>pH) e)=pR^r*pH^r := by
  have hd : Disjoint ((ordinaryWheelRim W).edgeFinset.image (Sum.inl (β:=V×U)))
      ((ordinaryWheelRim W).support.toFinset.image (fun v=>Sum.inr (v,ordinaryWheelHub W))) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp he
    obtain ⟨b,_,hh⟩:=Finset.mem_image.mp hf
    cases hh
  have hC : IsEmbeddedCycle (ordinaryWheelRim W) r := W.val.1.val.property
  unfold ordinaryWheelResources
  rw [Finset.prod_union hd,
    Finset.prod_image (by intro x _ y _ h;exact Sum.inl.inj h),
    Finset.prod_image (by intro x _ y _ h;exact (Prod.mk.inj (Sum.inr.inj h)).1)]
  simp only [Sum.elim_inl,Sum.elim_inr,Finset.prod_const,
    hC.edgeFinset_card,hC.support_card]

theorem ordinaryWheelResources_rim_omitted_product (W : OrdinaryWheel P F Hbase r)
    (hr : 1≤r) (pR pH : ℝ) (hpR : pR≠0) (e : Sym2 V)
    (he : Sum.inl e∈ordinaryWheelResources W) :
    (∏ a∈ordinaryWheelResources W\{Sum.inl e},Sum.elim (fun _=>pR) (fun _=>pH) a)=
      pR^(r-1)*pH^r := by
  have hh := Finset.mul_prod_erase (ordinaryWheelResources W)
    (Sum.elim (fun _=>pR) (fun _=>pH)) he
  have heq : (ordinaryWheelResources W).erase (Sum.inl e)=ordinaryWheelResources W\{Sum.inl e} := by
    ext a;simp [and_comm]
  rw [heq,ordinaryWheelResources_constant_product] at hh
  apply mul_left_cancel₀ hpR
  calc
    _ = pR^r*pH^r := hh
    _ = (pR*pR^(r-1))*pH^r := by rw [← pow_succ',Nat.sub_add_cancel hr]
    _ = _ := by ring

theorem ordinaryWheelResources_spoke_omitted_product (W : OrdinaryWheel P F Hbase r)
    (hr : 1≤r) (pR pH : ℝ) (hpH : pH≠0) (a : V×U)
    (ha : Sum.inr a∈ordinaryWheelResources W) :
    (∏ e∈ordinaryWheelResources W\{Sum.inr a},Sum.elim (fun _=>pR) (fun _=>pH) e)=
      pR^r*pH^(r-1) := by
  have hh := Finset.mul_prod_erase (ordinaryWheelResources W)
    (Sum.elim (fun _=>pR) (fun _=>pH)) ha
  have heq : (ordinaryWheelResources W).erase (Sum.inr a)=ordinaryWheelResources W\{Sum.inr a} := by
    ext e;simp [and_comm]
  rw [heq,ordinaryWheelResources_constant_product] at hh
  apply mul_left_cancel₀ hpH
  calc
    _ = pR^r*pH^r := hh
    _ = pR^r*(pH*pH^(r-1)) := by rw [← pow_succ',Nat.sub_add_cancel hr]
    _ = _ := by ring

theorem rawWheelMarginal_constant_on_candidate {Color : Type} (s : U → Color → ℝ)
    (j : Color) (pR pH : ℝ) (hs : ∀ u,s u j=pH) (W : OrdinaryWheel P F Hbase r)
    (a : Sym2 V⊕(V×U)) (ha : a∈ordinaryWheelResources W) :
    rawWheelMarginal P (fun _=>pR) s j a=Sum.elim (fun _=>pR) (fun _=>pH) a := by
  cases a with
  | inl e=>
    have he : e∈P.edgeSet := by
      rw [ordinaryWheelResources_rim] at ha
      induction e using Sym2.ind with
      | _ x y=>exact W.val.1.property ha
    simp only [rawWheelMarginal,he,ite_true,Sum.elim_inl]
  | inr a=>exact hs a.2

variable {Γ Color : Type} [Fintype Γ] [Fintype Color]
    (P F : SimpleGraph V) (Hbase : V → U → Prop) (r : ℕ) (hr : 1≤r)
    (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (hF : permutationConflictGraph π (3*d)≤F)
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (pR pH : ℝ) (hpR : 0<pR) (hpR1 : pR≤1) (hpH : 0<pH)
    (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (j : Color) (hj : ∀ u,s u j=pH)
    (w : OrdinaryWheel P F Hbase r → ℝ)

local notation "μwheel" => rawWheelLaw (fun _ : Sym2 V=>pR) (fun _=>hpR.le) (fun _=>hpR1) d hd q hq hQ s hs hS

include hr hF hnoshort hpH hj

theorem ordinaryRawPotentialLoad_rim_mean (x y : V) :
    (FiniteLaw.pi μwheel).expectation (fun σ=>
      ordinaryPotentialLoad w (Sum.inl s(x,y)) (rawWheelGraph P σ) (rawWheelSpokes π d σ j))=
      pR^(r-1)*pH^r*ordinaryRimLoad w x y := by
  rw [ordinaryRawPotentialLoad_expectation P π (fun _=>pR) (fun _=>hpR.le) (fun _=>hpR1)
    d hd q hq hQ s hs hS hnoshort F Hbase r hF w j]
  unfold ordinaryRimLoad
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro W _
  by_cases he : Sum.inl s(x,y)∈ordinaryWheelResources W
  · have hxy : (ordinaryWheelRim W).Adj x y := (ordinaryWheelResources_rim W _).mp he
    rw [if_pos he,if_pos hxy]
    have hh := Finset.prod_congr rfl (fun a (ha : a∈ordinaryWheelResources W\{Sum.inl s(x,y)})=>
      rawWheelMarginal_constant_on_candidate s j pR pH hj W a (Finset.mem_sdiff.mp ha).1)
    rw [hh,ordinaryWheelResources_rim_omitted_product W hr pR pH hpR.ne' _ he]
    ring
  · have hxy : ¬(ordinaryWheelRim W).Adj x y := fun h=>he ((ordinaryWheelResources_rim W _).mpr h)
    simp only [he,hxy,ite_false,zero_mul,mul_zero]

theorem ordinaryRawPotentialLoad_spoke_mean (v : V) (u : U) :
    (FiniteLaw.pi μwheel).expectation (fun σ=>
      ordinaryPotentialLoad w (Sum.inr (v,u)) (rawWheelGraph P σ) (rawWheelSpokes π d σ j))=
      pR^r*pH^(r-1)*ordinarySpokeLoad w v u := by
  rw [ordinaryRawPotentialLoad_expectation P π (fun _=>pR) (fun _=>hpR.le) (fun _=>hpR1)
    d hd q hq hQ s hs hS hnoshort F Hbase r hF w j]
  unfold ordinarySpokeLoad
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro W _
  by_cases he : Sum.inr (v,u)∈ordinaryWheelResources W
  · have hvu := (ordinaryWheelResources_spoke W v u).mp he
    rw [if_pos he,if_pos hvu]
    have hh := Finset.prod_congr rfl (fun a (ha : a∈ordinaryWheelResources W\{Sum.inr (v,u)})=>
      rawWheelMarginal_constant_on_candidate s j pR pH hj W a (Finset.mem_sdiff.mp ha).1)
    rw [hh,ordinaryWheelResources_spoke_omitted_product W hr pR pH hpH.ne' _ he]
    ring
  · have hvu : ¬(ordinaryWheelHub W=u ∧ v∈(ordinaryWheelRim W).support) :=
      fun h=>he ((ordinaryWheelResources_spoke W v u).mpr h)
    simp only [he,hvu,ite_false,zero_mul,mul_zero]

end Oberwolfach
