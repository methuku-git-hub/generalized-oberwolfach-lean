module

public import Oberwolfach.LocalFactorGraphChoice

@[expose] public section
/-! Transport selected local cycles to an actual host that retains their
factor graph; the physical cycles and their exact union stay unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

def localOrdinaryCycleToHost
    (Q Q' F:SimpleGraph V) (T:Finset V) (r:ℕ)
    (M:Finset (LocalOrdinaryCycle Q F T r)) (hsub:localOrdinaryFactorGraph M≤Q')
    (C:{C:LocalOrdinaryCycle Q F T r // C∈M}):LocalOrdinaryCycle Q' F T r:=
  ⟨⟨C.val.val.val,fun v w h=>hsub ((localOrdinaryFactorGraph_adj M v w).mpr ⟨C.val,C.property,h⟩)⟩,
    C.val.property⟩

theorem local_ordinary_factor_transfer_to_host
    (Q Q' F:SimpleGraph V) (T:Finset V) (r:ℕ)
    (M:Finset (LocalOrdinaryCycle Q F T r)) (hsub:localOrdinaryFactorGraph M≤Q'):
    ∃M':Finset (LocalOrdinaryCycle Q' F T r),
      ((∀C∈M',∀D∈M',C≠D→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices D)) ↔
        (∀C∈M,∀D∈M,C≠D→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices D))) ∧
      M'.biUnion localOrdinaryVertices=M.biUnion localOrdinaryVertices ∧
      localOrdinaryFactorGraph M'=localOrdinaryFactorGraph M:=by
  let f:=localOrdinaryCycleToHost Q Q' F T r M hsub
  let M':=Finset.univ.image f
  have hf:Function.Injective f:=by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c:LocalOrdinaryCycle Q' F T r=>c.val.val) hab
  refine ⟨M',?_,?_,?_⟩
  · constructor
    · intro h C hC D hD hne
      have hh:=h (f ⟨C,hC⟩) (Finset.mem_image.mpr ⟨⟨C,hC⟩,Finset.mem_univ _,rfl⟩)
        (f ⟨D,hD⟩) (Finset.mem_image.mpr ⟨⟨D,hD⟩,Finset.mem_univ _,rfl⟩)
        (by
          intro he
          apply hne
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun c:LocalOrdinaryCycle Q' F T r=>c.val.val) he)
      exact hh
    · intro h C hC D hD hne
      obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hC
      obtain ⟨b,_,rfl⟩:=Finset.mem_image.mp hD
      exact h a.val a.property b.val b.property (fun he=>hne (congrArg f (Subtype.ext he)))
  · ext v
    simp only [M',Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨_,⟨a,rfl⟩,hv⟩;exact ⟨a.val,a.property,hv⟩
    · rintro ⟨C,hC,hv⟩;exact ⟨f ⟨C,hC⟩,⟨⟨C,hC⟩,rfl⟩,hv⟩
  · ext v w
    rw [localOrdinaryFactorGraph_adj,localOrdinaryFactorGraph_adj]
    constructor
    · rintro ⟨C,hC,hvw⟩
      obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hC
      exact ⟨a.val,a.property,hvw⟩
    · rintro ⟨C,hC,hvw⟩
      exact ⟨f ⟨C,hC⟩,Finset.mem_image.mpr ⟨⟨C,hC⟩,Finset.mem_univ _,rfl⟩,hvw⟩
end Oberwolfach
