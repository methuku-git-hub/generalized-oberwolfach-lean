module

public import Oberwolfach.FactorDecompositionClasses

@[expose] public section
/-! Reindex nonempty classes without adding empty classes or changing the
prescribed factor attached to any retained index. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_decomposition_from_nonempty_class_reindex
    {n k:ℕ} {W J:Type} [Fintype W] [Fintype J] [DecidableEq J]
    (G:SimpleGraph (Fin n)) (F:W→SimpleGraph (Fin n)) (classify:W→J)
    (C:Finset J) (eC:Fin k≃↥C) (hcover:∀w,classify w∈C)
    (m:Fin k→ℕ) (eF:∀a,Fin (m a)≃{w:W // classify w=(eC a).val})
    (H:Fin k→SimpleGraph (Fin n)) (hpart:EdgePartition G H)
    (hdec:∀a,HasFactorDecomposition (H a) (fun i=>F ((eF a i).val))):
    HasFactorDecomposition G (fun i:Fin (Fintype.card W)=>F ((Fintype.equivFin W).symm i)) :=by
  let eW:Fin (Fintype.card W)≃W:=(Fintype.equivFin W).symm
  let cw:W→Fin k:=fun w=>eC.symm ⟨classify w,hcover w⟩
  let colour:Fin (Fintype.card W)→Fin k:=fun i=>cw (eW i)
  apply factor_decomposition_from_classes G (fun i=>F (eW i)) H colour hpart
  intro a
  obtain ⟨pieces,hpieces,hiso⟩:=hdec a
  have hfiber (i:{i:Fin (Fintype.card W) // colour i=a}):classify (eW i.val)=(eC a).val:=by
    have h:=congrArg (fun t:Fin k=>(eC t).val) i.property
    simpa only [colour,cw,Equiv.apply_symm_apply] using h
  let f:{i:Fin (Fintype.card W) // colour i=a}→Fin (m a):=fun i=>(eF a).symm ⟨eW i.val,hfiber i⟩
  have hinj:Function.Injective f:=by
    intro i j hij
    have hh:=congrArg (eF a) hij
    have hw:eW i.val=eW j.val:=by simpa only [f,Equiv.apply_symm_apply] using congrArg Subtype.val hh
    exact Subtype.ext (eW.injective hw)
  refine ⟨fun i=>pieces (f i),?_,?_,?_⟩
  · intro x y
    constructor
    · intro hxy
      obtain ⟨j,hj⟩:=((hpieces x y).1).mp hxy
      let w:{w:W // classify w=(eC a).val}:=eF a j
      let i:Fin (Fintype.card W):=eW.symm w.val
      have hi:colour i=a:=by
        apply eC.injective
        apply Subtype.ext
        simpa only [colour,cw,Equiv.apply_symm_apply,i,Equiv.apply_symm_apply] using w.property
      refine ⟨⟨i,hi⟩,?_⟩
      have hfi:f ⟨i,hi⟩=j:=by
        apply (eF a).injective
        apply Subtype.ext
        simp only [f,Equiv.apply_symm_apply,i,Equiv.apply_symm_apply,w]
      simpa only [hfi] using hj
    · rintro ⟨i,hi⟩
      exact ((hpieces x y).1).mpr ⟨f i,hi⟩
  · intro i j x y hi hj
    exact hinj ((hpieces x y).2 (f i) (f j) hi hj)
  · intro i
    have h:=hiso (f i)
    have hi:(eF a (f i)).val=eW i.val:=by simp only [f,Equiv.apply_symm_apply]
    simpa only [hi] using h
end Oberwolfach
