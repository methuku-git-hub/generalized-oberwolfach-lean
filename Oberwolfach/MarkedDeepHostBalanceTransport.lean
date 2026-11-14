module

public import Oberwolfach.MarkedReservedCanonicalCombinedDeletion
public import Oberwolfach.MarkedReservedDeepHost

@[expose] public section
/-! Balance and cleared-neighbourhood conditions depend only on the actual
raw outcome and typed spoke relations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
def MarkedDeepHostBalanced (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (I T:Finset V) (J W:Finset U):Prop:=
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let src:=Sum.elim (fun e:E=>e.val.1) (fun e:K=>e.val.1)
    let dst:=Sum.elim (fun e:E=>e.val.2) (fun e:K=>e.val.2);
    (∀ v∈T,
      (Finset.univ.filter (fun a=>dst a=v)).card=(Finset.univ.filter (fun a=>src a=v)).card ∧
      (Finset.univ.filter (fun a=>dst a=v)).card=
        (Finset.univ.filter (fun z:V×U=>(H false z.1 z.2∨H true z.1 z.2)∧z.1=v)).card ∧
      (Finset.univ.filter (fun a=>dst a=v∧markedArcType a=true)).card=
        (Finset.univ.filter (fun z:V×U=>H true z.1 z.2∧z.1=v)).card) ∧
    (∀ u∈W,Fintype.card (hubNeighbourClass (H false) (H true) u false)=
      m*Fintype.card (hubNeighbourClass (H false) (H true) u true)) ∧
    (∀ a:E⊕K,dst a∈T→src a∉I) ∧
    (∀ a:E⊕K,src a∈T→dst a∉I) ∧
    (∀ x∈T,∀ u,H false x u∨H true x u→u∉J) ∧
    (∀ u∈W,∀ x,H false x u∨H true x u→x∉I)

omit [Fintype Γ] [Fintype Color] [DecidableEq U] in
theorem marked_deep_host_balance_transport
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ σ':RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (I T:Finset V) (J W:Finset U) (hσ:σ=σ') (hH:H=H'):
    MarkedDeepHostBalanced P π d m σ H I T J W ↔
      MarkedDeepHostBalanced P π d m σ' H' I T J W:=by
  subst σ'
  subst H'
  rfl
end Oberwolfach
