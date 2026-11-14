module

public import Oberwolfach.DirectedBoundaryIncidences
public import Oberwolfach.MarkedWheelResources
public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section

/-! Actual typed arcs and spokes give injective physical boundary coins.
Directions and the marked permutation are retained when assigning each
crossing edge to its outside auxiliary endpoint. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

def markedArcPhysicalCoin (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V):E⊕K→Sym2 V :=
  Sum.elim (fun e=>s(tail e,head e)) (fun e=>s(ktail e,π (khead e)))

theorem markedArcPhysicalCoin_toFinset (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (a:E⊕K):
    (markedArcPhysicalCoin tail head ktail khead π a).toFinset=
      markedPhysicalEdge tail head ktail khead π a := by
  cases a <;> exact Sym2.toFinset_mk_eq

theorem markedArcPhysicalCoin_injective (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)):
    Function.Injective (markedArcPhysicalCoin tail head ktail khead π) := by
  intro a b hab
  apply hp
  simpa only [markedArcPhysicalCoin_toFinset] using congrArg Sym2.toFinset hab

def markedActivePhysicalCoin (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (H₀ HK:V→U→Prop):MarkedActiveEdge E K H₀ HK→Sym2 (V⊕U) :=
  fun a=>ordinaryPhysicalResource (Sum.elim
    (fun a=>Sum.inl (markedArcPhysicalCoin tail head ktail khead π a))
    (fun vu=>Sum.inr vu.val) a)

theorem markedActivePhysicalCoin_injective (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (H₀ HK:V→U→Prop) (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)):
    Function.Injective (markedActivePhysicalCoin tail head ktail khead π H₀ HK) := by
  intro a b hab
  have hh:=ordinaryPhysicalResource_injective hab
  rcases a with a|a <;> rcases b with b|b
  · exact congrArg Sum.inl (markedArcPhysicalCoin_injective tail head ktail khead π hp (Sum.inl.inj hh))
  · exact (Sum.inl_ne_inr hh).elim
  · exact (Sum.inr_ne_inl hh).elim
  · exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj hh))

def markedActiveAuxTail (tail:E→V) (ktail:K→V) (H₀ HK:V→U→Prop):MarkedActiveEdge E K H₀ HK→V⊕U :=
  Sum.elim (Sum.elim (fun a=>Sum.inl (tail a)) (fun a=>Sum.inl (ktail a))) (fun vu=>Sum.inl vu.val.1)
def markedActiveAuxHead (head:E→V) (khead:K→V) (H₀ HK:V→U→Prop):MarkedActiveEdge E K H₀ HK→V⊕U :=
  Sum.elim (Sum.elim (fun a=>Sum.inl (head a)) (fun a=>Sum.inl (khead a))) (fun vu=>Sum.inr vu.val.2)
def markedActiveDirectionTag (H₀ HK:V→U→Prop):MarkedActiveEdge E K H₀ HK→Fin 3 :=
  Sum.elim (Sum.elim (fun _=>0) (fun _=>1)) (fun _=>2)

theorem markedActive_typed_endpoints_injective (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (H₀ HK:V→U→Prop) (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)):
    Function.Injective (fun a:MarkedActiveEdge E K H₀ HK=>
      (markedActiveDirectionTag H₀ HK a,markedActiveAuxTail tail ktail H₀ HK a,markedActiveAuxHead head khead H₀ HK a)) := by
  obtain ⟨hinE,hinK⟩:=markedPhysicalEdge_endpoint_injections tail head ktail khead π hp
  intro a b hab
  rcases a with (a|a)|a <;> rcases b with (b|b)|b
  all_goals simp only [markedActiveDirectionTag,markedActiveAuxTail,markedActiveAuxHead,Sum.elim_inl,Sum.elim_inr,
    Prod.mk.injEq,Sum.inl.injEq,Sum.inr.injEq] at hab
  · exact congrArg (fun e:E=>Sum.inl (Sum.inl e)) (hinE (Prod.ext hab.2.1 hab.2.2))
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · exact congrArg (fun e:K=>Sum.inl (Sum.inr e)) (hinK (Prod.ext hab.2.1 hab.2.2))
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · exact congrArg Sum.inr (Subtype.ext (Prod.ext hab.2.1 hab.2.2))

end Oberwolfach
