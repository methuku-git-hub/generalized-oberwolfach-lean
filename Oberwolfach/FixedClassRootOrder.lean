module

public import Oberwolfach.FixedClassMarkedCycles

@[expose] public section

/-! Order an arbitrary root set with profile (1,m), placing its unique
marked-class vertex first. No separation or cycle existence is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

 theorem fixed_class_root_order (m:ℕ) (A B X:Finset V) (hAB:Disjoint A B)
    (hX:X⊆A∪B) (hA:(X∩A).card=1) (hB:(X∩B).card=m):
    ∃ x:Fin (m+1)→V,Function.Injective x∧Finset.univ.image x=X∧x 0∈A∧∀ i:Fin m,x i.succ∈B:=by
  obtain ⟨a,ha⟩:=Finset.card_eq_one.mp hA
  have haX:a∈X∩A:=by rw [ha];simp
  let e:Fin m≃{v:V // v∈X∩B}:=(Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hB)).symm
  let x:Fin (m+1)→V:=Fin.cons a (fun i=>(e i).val)
  have haB:a∉B:=fun h=>Finset.disjoint_left.mp hAB (Finset.mem_inter.mp haX).2 h
  have hx:Function.Injective x:=by
    intro i j hij
    revert j
    refine Fin.cases ?_ (fun i=>?_) i
    · intro j hij
      revert hij
      refine Fin.cases (fun _=>rfl) (fun j hij=>?_) j
      have he:a=(e j).val:=hij
      exact False.elim (haB (he.symm ▸ (Finset.mem_inter.mp (e j).property).2))
    · intro j hij
      revert hij
      refine Fin.cases (fun hij=>?_) (fun j hij=>?_) j
      · have he:(e i).val=a:=hij
        exact False.elim (haB (he ▸ (Finset.mem_inter.mp (e i).property).2))
      · exact congrArg Fin.succ (e.injective (Subtype.ext hij))
  have hset:Finset.univ.image x=X:=by
    ext v
    constructor
    · intro hv
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hv
      refine Fin.cases ?_ (fun i=>?_) i
      · exact (Finset.mem_inter.mp haX).1
      · exact (Finset.mem_inter.mp (e i).property).1
    · intro hv
      rcases Finset.mem_union.mp (hX hv) with hvA|hvB
      · have he:v=a:=by have hh: v∈X∩A:=Finset.mem_inter.mpr ⟨hv,hvA⟩;rw [ha] at hh;exact Finset.mem_singleton.mp hh
        exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,he.symm⟩
      · let w:{v:V // v∈X∩B}:=⟨v,Finset.mem_inter.mpr ⟨hv,hvB⟩⟩
        refine Finset.mem_image.mpr ⟨(e.symm w).succ,Finset.mem_univ _,?_⟩
        change (e (e.symm w)).val=v
        rw [e.apply_symm_apply]
  exact ⟨x,hx,hset,(Finset.mem_inter.mp haX).2,fun i=>(Finset.mem_inter.mp (e i).property).2⟩

end Oberwolfach
