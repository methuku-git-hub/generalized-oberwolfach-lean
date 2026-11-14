module

public import Oberwolfach.BufferedFinalEndpointGeometry

@[expose] public section
/-! Initial endpoints of disjoint buffered paths are distinct and lie outside
all strict path interiors. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def bufferedInitialEndpoints {X I:Type*} [Fintype I] [DecidableEq X]
    (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X) : Finset X :=
  Finset.univ.image (fun i=>inner i (0))

theorem buffered_initial_endpoints_disjoint_strict
    {X I:Type*} [Fintype I] [DecidableEq X]
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪X) (inner:∀i,Fin (n i+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j))) :
    Disjoint (bufferedInitialEndpoints n inner) (bufferedPathStrictInterior n inner) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
  rcases Finset.mem_biUnion.mp hy with ⟨j,_,hj⟩
  obtain ⟨p,hp,heq⟩:=Finset.mem_image.mp hj
  have hp':=(Finset.mem_filter.mp hp).2
  by_cases hij:i=j
  · subst j
    have he:p=0:=(inner i).injective heq
    have heval:p.val=0:=congrArg Fin.val he
    omega
  · have hi:inner i (0)∈Finset.univ.image (inner i):=
      Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
    have hj':inner i (0)∈Finset.univ.image (inner j):=
      Finset.mem_image.mpr ⟨p,Finset.mem_univ _,heq⟩
    exact Finset.disjoint_left.mp (buffered_inner_domains_disjoint n ext inner hinner hdis i j hij) hi hj'

theorem buffered_initial_endpoints_card
    {X I:Type*} [Fintype I] [DecidableEq X]
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪X) (inner:∀i,Fin (n i+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j))) :
    (bufferedInitialEndpoints n inner).card=Fintype.card I := by
  classical
  unfold bufferedInitialEndpoints
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j heq
    by_contra hij
    have hi:inner i (0)∈Finset.univ.image (inner i):=
      Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
    have hj:inner i (0)∈Finset.univ.image (inner j):=
      Finset.mem_image.mpr ⟨0,Finset.mem_univ _,heq.symm⟩
    exact Finset.disjoint_left.mp (buffered_inner_domains_disjoint n ext inner hinner hdis i j hij) hi hj
end Oberwolfach
