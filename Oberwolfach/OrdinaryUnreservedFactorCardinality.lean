module

public import Oberwolfach.OrdinaryReservedSpokeCardinality

@[expose] public section
/-! Exact order of the factor remaining after the reserved equal-size cycle
components are removed. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_unreserved_factor_cardinality
    {n r:ℕ} (F:SimpleGraph (Fin n)) (C:Finset F.ConnectedComponent)
    (hsize:∀c:↥C,Fintype.card c.val=r):
    Fintype.card {x:Fin n // F.connectedComponentMk x∉C}+r*C.card=n:=by
  classical
  let S:={x:Fin n // F.connectedComponentMk x∉C}
  let f:S↪Fin n:=⟨Subtype.val,Subtype.val_injective⟩
  let T:Finset (Fin n):=Finset.univ.image f
  have hT:T.card=Fintype.card S:=by
    dsimp [T]
    rw [Finset.card_image_of_injective _ f.injective]
    exact Finset.card_univ
  have hcard:=ordinary_reserved_spoke_cardinality F C hsize f (fun v=>v∉Set.range f) (fun _=>Iff.rfl)
  have hcompl:(Finset.univ.filter (fun v=>v∉Set.range f))=Tᶜ:=by
    ext v
    simp [T]
  have hcard':(Tᶜ).card=r*C.card:=by
    convert hcard.1 using 1 <;> congr 1 <;> ext v <;> simp [T]
  rw [Finset.card_compl,Fintype.card_fin,hT] at hcard' 
  have hle:Fintype.card S≤n:=by simpa only [Fintype.card_fin] using Fintype.card_subtype_le (p:=fun x:Fin n=>F.connectedComponentMk x∉C)
  change Fintype.card S+r*C.card=n
  omega
end Oberwolfach
