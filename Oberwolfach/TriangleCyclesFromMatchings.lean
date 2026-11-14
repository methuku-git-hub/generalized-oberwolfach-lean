module

public import Oberwolfach.OrdinaryLocalCycles
public import Oberwolfach.CycleVertexMatchingWeights
public import Oberwolfach.ResourceDecompositions

@[expose] public section

/-! Convert the two tripartite matching bijections into an exact factor by
actual, unordered triangle subgraphs of the original graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem triangle_cycle_from_vertices (G : SimpleGraph V) (u v w : V)
    (huv : u≠v) (huw : u≠w) (hvw : v≠w)
    (huvG : G.Adj u v) (huwG : G.Adj u w) (hvwG : G.Adj v w) :
    ∃ C : OrdinaryCycle G 3,ordinaryCycleVertices G 3 C=Finset.univ.image (![u,v,w] : Fin 3→V) := by
  have hq1:=huvG.symm
  have hq2:=huwG.symm
  have hq3:=hvwG.symm
  have hi : Function.Injective (![u,v,w] : Fin 3→V) := by
    intro i j h;fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨C,hC⟩ := ordinary_cycle_from_embedding G ⊥ Finset.univ (by norm_num : 3≤3)
    ⟨![u,v,w],hi⟩ (fun _=>Finset.mem_univ _) (by simp)
    (by intro i j h;have hn:=h.ne;fin_cases i <;> fin_cases j <;> simp_all)
  exact ⟨C.val,hC⟩

theorem triangle_factor_from_bijections (G : SimpleGraph V) (c : V→Fin 3)
    (σ : {v // c v=0}≃{v // c v=1}) (τ : {v // c v=0}≃{v // c v=2})
    (hG : ∀ x,G.Adj x.val (σ x).val ∧ G.Adj x.val (τ x).val ∧ G.Adj (σ x).val (τ x).val) :
    HasResourceDecomposition (ordinaryCycleVertices G 3) Finset.univ := by
  let X := {v // c v=0}
  let f : X→Fin 3→V := fun x=>![x.val,(σ x).val,(τ x).val]
  have hcolour (x : X) (i : Fin 3) : c (f x i)=i := by
    fin_cases i
    · exact x.property
    · exact (σ x).property
    · exact (τ x).property
  have hjoint : Function.Injective (fun p : X×Fin 3=>f p.1 p.2) := by
    rintro ⟨x,i⟩ ⟨y,j⟩ he
    have hij : i=j := (hcolour x i).symm.trans ((congrArg c he).trans (hcolour y j))
    subst j
    have hxy : x=y := by
      fin_cases i
      · exact Subtype.ext he
      · exact σ.injective (Subtype.ext he)
      · exact τ.injective (Subtype.ext he)
    exact Prod.ext hxy rfl
  have hsurj : Function.Surjective (fun p : X×Fin 3=>f p.1 p.2) := by
    intro v
    generalize hh : c v=i
    fin_cases i
    · exact ⟨(⟨v,hh⟩,0),rfl⟩
    · refine ⟨(σ.symm ⟨v,hh⟩,1),?_⟩
      change (σ (σ.symm ⟨v,hh⟩)).val=v
      rw [σ.apply_symm_apply]
    · refine ⟨(τ.symm ⟨v,hh⟩,2),?_⟩
      change (τ (τ.symm ⟨v,hh⟩)).val=v
      rw [τ.apply_symm_apply]
  have hex (x : X) : ∃ C : OrdinaryCycle G 3,ordinaryCycleVertices G 3 C=Finset.univ.image (f x) := by
    have hi : Function.Injective (f x) := fun i j h=>congrArg Prod.snd (hjoint (a₁:=(x,i)) (a₂:=(x,j)) h)
    have h01 : f x 0≠f x 1 := fun h=>by have hh:=hi h;norm_num at hh
    have h02 : f x 0≠f x 2 := fun h=>by have hh:=hi h;norm_num at hh
    have h12 : f x 1≠f x 2 := fun h=>by have hh:=hi h;norm_num at hh
    exact triangle_cycle_from_vertices G _ _ _ h01 h02 h12 (hG x).1 (hG x).2.1 (hG x).2.2
  let C : X→OrdinaryCycle G 3 := fun x=>Classical.choose (hex x)
  have hC (x) : ordinaryCycleVertices G 3 (C x)=Finset.univ.image (f x) := Classical.choose_spec (hex x)
  refine ⟨Finset.univ.image C,?_,?_⟩
  · intro D hD E hE hne
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hE
    apply Finset.disjoint_left.mpr
    intro v hv hw
    rw [hC] at hv hw
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hv
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hw
    have hxy := congrArg Prod.fst (hjoint (a₁:=(x,i)) (a₂:=(y,j)) (hi.trans hj.symm))
    exact hne (congrArg C hxy)
  · apply Finset.eq_univ_of_forall
    intro v
    obtain ⟨⟨x,i⟩,he⟩ := hsurj v
    apply Finset.mem_biUnion.mpr
    refine ⟨C x,Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩,?_⟩
    rw [hC]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he⟩

end Oberwolfach
