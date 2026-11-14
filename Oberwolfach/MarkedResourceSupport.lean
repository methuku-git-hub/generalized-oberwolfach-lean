module

public import Oberwolfach.MarkedHubFactorTrade
public import Oberwolfach.MarkedTransformerWheelPacking

@[expose] public section

/-! Auxiliary row support for actual physical resources. A marked physical
head may lie outside the row support; disjointness is therefore proved by
pulling edges back through the fixed injective representation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 11000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V}

 def MarkedResourceSupported (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (T:Finset V):Finset V⊕(V×U)→Prop
  | .inl e=>∃ a:E⊕K,markedPhysicalEdge tail head ktail khead π a=e∧
      Sum.elim tail ktail a∈T∧Sum.elim head khead a∈T
  | .inr vu=>vu.1∈T

 theorem marked_resource_support_mono {T T':Finset V} (h:T⊆T')
    (e:Finset V⊕(V×U)) (he:MarkedResourceSupported tail head ktail khead π T e):
    MarkedResourceSupported tail head ktail khead π T' e:=by
  cases e with
  | inl e=>obtain ⟨a,ha,h₁,h₂⟩:=he;exact ⟨a,ha,h h₁,h h₂⟩
  | inr vu=>exact h he

 theorem marked_resource_sets_disjoint
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (T T':Finset V) (hT:Disjoint T T') (P Q:Finset (Finset V⊕(V×U)))
    (hP:∀ e∈P,MarkedResourceSupported tail head ktail khead π T e)
    (hQ:∀ e∈Q,MarkedResourceSupported tail head ktail khead π T' e):Disjoint P Q:=by
  apply Finset.disjoint_left.mpr
  intro e he hf
  cases e with
  | inl e=>
    obtain ⟨a,ha,h₁,h₂⟩:=hP _ he
    obtain ⟨b,hb,h₃,h₄⟩:=hQ _ hf
    have hab:a=b:=hp (ha.trans hb.symm)
    exact Finset.disjoint_left.mp hT h₁ (hab.symm ▸ h₃)
  | inr vu=>exact Finset.disjoint_left.mp hT (hP _ he) (hQ _ hf)

 theorem marked_cycle_at_hub_supported {m b:ℕ}
    (C:MarkedCycleTuple tail head ktail khead m π b) (u:U) (T:Finset V)
    (hT:∀ i,C.val i∈T):
    ∀ e∈markedCycleResourcesAtHub C u,MarkedResourceSupported tail head ktail khead π T e:=by
  intro e he
  rcases Finset.mem_union.mp he with he|he
  · obtain ⟨f,hf,rfl⟩:=Finset.mem_image.mp he
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hf
    have hi':=markedCycleTypedEdge_endpoints tail head ktail khead m π b C i
    exact ⟨markedCycleTypedEdge tail head ktail khead m π b C i,hi,
      hi'.1.symm ▸ hT i,hi'.2.symm ▸ hT (finRotate (m+1) i)⟩
  · obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp he
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hv
    exact hT i

 theorem marked_factor_at_hub_supported {m b:ℕ}
    (M:Finset (MarkedCycleTuple tail head ktail khead m π b)) (u:U) (T:Finset V)
    (hT:M.biUnion (fun C=>Finset.univ.image C.val)⊆T):
    ∀ e∈M.biUnion (fun C=>markedCycleResourcesAtHub C u),
      MarkedResourceSupported tail head ktail khead π T e:=by
  intro e he
  obtain ⟨C,hC,he⟩:=Finset.mem_biUnion.mp he
  exact marked_cycle_at_hub_supported C u T (fun i=>hT (Finset.mem_biUnion.mpr
    ⟨C,hC,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)) e he

end Oberwolfach
