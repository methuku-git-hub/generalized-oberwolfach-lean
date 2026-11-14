module

public import Oberwolfach.TypedMarkedPotentialResources

@[expose] public section

/-! Exact products on a canonical wheel and with one specified typed root
removed. These formulas keep the ordinary and marked spoke types distinct. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E K : Type*} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head : E→V} {ktail khead : K→V} {m b : ℕ} {π : Equiv.Perm V}
  {H₀ Hₖ : V→U→Prop}

theorem typedMarkedResource_product
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (φ : (E⊕K)⊕(Bool×V×U)→ℝ) (p k s t : ℝ)
    (hR : ∀ i,φ (Sum.inl (markedCycleTypedEdge tail head ktail khead m π b W.1 i))=
      if i=Fin.last m then k else p)
    (hH : ∀ i,φ (Sum.inr (decide (i=0),W.1.val i,W.2.val))=if i=0 then t else s) :
    (∏ a∈typedMarkedOccurrenceResources W,φ a)=(p^m*k)*(t*s^m) := by
  have he : Finset.univ.filter (fun e=>CanonicalMarkedArcMem W.1 e)=
      Finset.univ.image (markedCycleTypedEdge tail head ktail khead m π b W.1) := by
    ext e;simp [CanonicalMarkedArcMem]
  have hdis : Disjoint
      ((Finset.univ.filter (fun e=>CanonicalMarkedArcMem W.1 e)).image (Sum.inl (β:=Bool×V×U)))
      (Finset.univ.image (fun i=>Sum.inr (α:=E⊕K) (decide (i=0),W.1.val i,W.2.val))) := by
    simp only [Finset.disjoint_left,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
    rintro a ⟨e,_,rfl⟩ ⟨i,hi⟩
    cases hi
  rw [typedMarkedOccurrenceResources,Finset.prod_union hdis,
    Finset.prod_image (fun _ _ _ _ h=>Sum.inl.inj h),he,
    Finset.prod_image (fun _ _ _ _ h=>markedCycleTypedEdge_injective tail head ktail khead m π b W.1 h),
    Finset.prod_image (fun i _ j _ h=>permutationSeparated_injective π b W.1.val W.1.property.1
      (congrArg (fun a : Bool×V×U=>a.2.1) (Sum.inr.inj h)))]
  simp_rw [hR,hH]
  rw [Fin.prod_univ_castSucc (fun i : Fin (m+1)=>if i=Fin.last m then k else p),
    Fin.prod_univ_succ (fun i : Fin (m+1)=>if i=0 then t else s)]
  simp

theorem typedMarkedResource_product_omitted
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (φ : (E⊕K)⊕(Bool×V×U)→ℝ) (p k s t : ℝ)
    (hR : ∀ i,φ (Sum.inl (markedCycleTypedEdge tail head ktail khead m π b W.1 i))=
      if i=Fin.last m then k else p)
    (hH : ∀ i,φ (Sum.inr (decide (i=0),W.1.val i,W.2.val))=if i=0 then t else s)
    (root : (E⊕K)⊕(Bool×V×U)) (hroot : root∈typedMarkedOccurrenceResources W)
    (hφ : φ root≠0) :
    (∏ a∈typedMarkedOccurrenceResources W\{root},φ a)=(p^m*k)*(t*s^m)/φ root := by
  apply (eq_div_iff hφ).mpr
  have hh := Finset.prod_sdiff (f:=φ) (Finset.singleton_subset_iff.mpr hroot)
  simp only [Finset.prod_singleton] at hh
  exact hh.trans (typedMarkedResource_product W φ p k s t hR hH)

end Oberwolfach
