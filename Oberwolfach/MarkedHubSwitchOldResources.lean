module

public import Oberwolfach.MarkedForbiddenResourceRows

@[expose] public section

/-! The exact hub-switch identity fixes the spokes on every retained root.
Together with auxiliary support it proves disjointness from the earlier
wheel families on the opposite side of the transformer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V}

 theorem marked_switch_root_spokes (Y Z:Finset V) (u u':U) (hu:u≠u')
    (P N:Finset (Finset V⊕(V×U)))
    (hs:∀ e∈P∪N,MarkedSwitchResource tail head ktail khead π Y Z u u' e)
    (hid:∀ e,(if e∈P then (1:ℤ) else 0)-(if e∈N then 1 else 0)=
      (if e∈Z.image (fun v=>Sum.inr (v,u)) then 1 else 0)-
      (if e∈Z.image (fun v=>Sum.inr (v,u')) then 1 else 0)):
    ∀ v∈Z,∀ z:U,((Sum.inr (v,z):Finset V⊕(V×U))∈P↔z=u)∧
      ((Sum.inr (v,z):Finset V⊕(V×U))∈N↔z=u'):=by
  intro v hv z
  have hmem (a:U):(Sum.inr (v,z):Finset V⊕(V×U))∈Z.image (fun x=>Sum.inr (x,a))↔z=a:=by
    simp only [Finset.mem_image,Sum.inr.injEq,Prod.mk.injEq]
    constructor
    · rintro ⟨x,_,rfl,ha⟩;exact ha.symm
    · intro ha;exact ⟨v,hv,rfl,ha.symm⟩
  have h:=hid (Sum.inr (v,z))
  simp only [hmem u,hmem u'] at h
  have hh:(Sum.inr (v,z):Finset V⊕(V×U))∈P∨(Sum.inr (v,z):Finset V⊕(V×U))∈N→z=u∨z=u':=by
    intro he
    exact (hs _ (Finset.mem_union.mpr he)).2
  clear hid hs hmem
  by_cases hzu:z=u <;> by_cases hzu':z=u' <;>
    by_cases hp:(Sum.inr (v,z):Finset V⊕(V×U))∈P <;>
    by_cases hn:(Sum.inr (v,z):Finset V⊕(V×U))∈N <;> simp_all

 theorem marked_switch_side_avoids_old_resources
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (Y Z W:Finset V) (u u':U) (hY:Disjoint Y W)
    (P Q:Finset (Finset V⊕(V×U)))
    (hQ:∀ e∈Q,MarkedResourceSupported tail head ktail khead π W e)
    (hP:∀ e∈P,MarkedSwitchResource tail head ktail khead π Y Z u u' e)
    (hroot:∀ v∈Z,∀ z:U,(Sum.inr (v,z):Finset V⊕(V×U))∈P→z=u)
    (hZ:∀ v∈Z,(Sum.inr (v,u):Finset V⊕(V×U))∉Q):Disjoint P Q:=by
  apply Finset.disjoint_left.mpr
  intro e he hf
  cases e with
  | inl e=>
    obtain ⟨a,ha,_,_,hnew⟩:=hP _ he
    obtain ⟨a',ha',h₁,h₂⟩:=hQ _ hf
    have haa:a=a':=hp (ha.trans ha'.symm)
    subst a'
    rcases hnew with hv|hv
    · exact Finset.disjoint_left.mp hY hv h₁
    · exact Finset.disjoint_left.mp hY hv h₂
  | inr vu=>
    have hrow:=hQ _ hf
    rcases Finset.mem_union.mp (hP _ he).1 with hv|hv
    · exact Finset.disjoint_left.mp hY hv hrow
    · have hh:=hroot vu.1 hv vu.2 he
      exact hZ vu.1 hv (hh ▸ hf)

end Oberwolfach
