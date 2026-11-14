module

public import Oberwolfach.ComponentFamilyDomainCard

@[expose] public section
/-! If the remaining spokes are exactly the vertices unused by the embedded
complement, their count is the total size of the reserved components. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reserved_spoke_cardinality {n r:ℕ}
    (F:SimpleGraph (Fin n)) (C:Finset F.ConnectedComponent)
    (hsize:∀c:↥C,Fintype.card c.val=r)
    (fC:{x:Fin n // F.connectedComponentMk x∉C}↪Fin n)
    (H:Fin n→Prop) (hH:∀v,H v↔v∉Set.range fC):
    (Finset.univ.filter H).card=r*C.card ∧
    (∀x,H (fC x)→False) :=by
  classical
  let A:Fin n→Prop:=fun x=>F.connectedComponentMk x∈C
  have hpred:∀x:Fin n,A x↔∃c:↥C,x∈c.val.supp:=by
    intro x
    constructor
    · intro hx;exact ⟨⟨F.connectedComponentMk x,hx⟩,rfl⟩
    · rintro ⟨c,hc⟩
      change F.connectedComponentMk x=c.val at hc
      dsimp [A];rw [hc];exact c.property
  let e:{x:Fin n // A x}≃{x:Fin n // ∃c:↥C,x∈c.val.supp}:={
    toFun:=fun x=>⟨x.val,(hpred x.val).1 x.property⟩
    invFun:=fun x=>⟨x.val,(hpred x.val).2 x.property⟩
    left_inv:=by intro x;apply Subtype.ext;rfl
    right_inv:=by intro x;apply Subtype.ext;rfl }
  have hSel:Fintype.card {x:Fin n // A x}=r*C.card:=by
    calc
      _ = Fintype.card {x:Fin n // ∃c:↥C,x∈c.val.supp}:=Fintype.card_congr e
      _ = ∑c:↥C,Fintype.card c.val:=component_family_domain_card F (fun c:↥C=>c.val) Subtype.val_injective
      _ = C.card*r:=by simp [hsize,Fintype.card_coe]
      _ = r*C.card:=Nat.mul_comm _ _
  let T:Finset (Fin n):=Finset.univ.image fC
  have hT:T.card=Fintype.card {x:Fin n // ¬A x}:=by
    dsimp [T]
    rw [Finset.card_image_of_injective _ fC.injective]
    simp only [Finset.card_univ]
    apply Fintype.card_congr
    exact Equiv.refl _
  have hcompl:Fintype.card {x:Fin n // ¬A x}=n-Fintype.card {x:Fin n // A x}:=by
    rw [Fintype.card_subtype_compl,Fintype.card_fin]
  have hcardA:Fintype.card {x:Fin n // A x}≤n:=by
    simpa using Fintype.card_subtype_le (p:=A)
  have hHset:Finset.univ.filter H=Tᶜ:=by
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_compl,T,Finset.mem_image]
    rw [hH]
    simp
  constructor
  · rw [hHset,Finset.card_compl,Fintype.card_fin,hT,hcompl,hSel]
    omega
  · intro x hx
    exact ((hH (fC x)).1 hx) ⟨x,rfl⟩
end Oberwolfach
