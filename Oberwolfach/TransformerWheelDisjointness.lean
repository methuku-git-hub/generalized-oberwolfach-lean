module

public import Oberwolfach.OrdinaryWheelDisjointness

@[expose] public section

/-! Physical disjointness from private path supports and checked old-root
edges. The test permits several old roots in a wheel and repeated hubs;
those possible overlaps are checked explicitly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

 theorem private_support_intersection (R A B:Finset V) (hAB:Disjoint A B)
    (hAR:Disjoint A R) (hBR:Disjoint B R) (x:V)
    (hxA:x∈R∪A) (hxB:x∈R∪B):x∈R:=by
  by_contra hx
  exact Finset.disjoint_left.mp hAB ((Finset.mem_union.mp hxA).resolve_left hx)
    ((Finset.mem_union.mp hxB).resolve_left hx)

 theorem transformer_wheel_pair_disjoint (W W':OrdinaryWheel Q F H r)
    (R S S':Finset V) (hSS:Disjoint S S')
    (hSR:Disjoint S R) (hS'R:Disjoint S' R)
    (hW:∀ x∈(ordinaryWheelRim W).support,x∈R∪S)
    (hW':∀ x∈(ordinaryWheelRim W').support,x∈R∪S')
    (hrim:∀ x∈R,∀ y∈R,¬((ordinaryWheelRim W).Adj x y∧(ordinaryWheelRim W').Adj x y))
    (hspoke:ordinaryWheelHub W=ordinaryWheelHub W'→
      ∀ x∈R,¬(x∈(ordinaryWheelRim W).support∧x∈(ordinaryWheelRim W').support)):
    Disjoint (ordinaryWheelResources W) (ordinaryWheelResources W'):=by
  apply (ordinaryWheelResources_disjoint_iff W W').mpr
  constructor
  · apply disjoint_iff_inf_le.mpr
    intro x y h
    have hx:=private_support_intersection R S S' hSS hSR hS'R x
      (hW x h.1.mem_support_left) (hW' x h.2.mem_support_left)
    have hy:=private_support_intersection R S S' hSS hSR hS'R y
      (hW y h.1.mem_support_right) (hW' y h.2.mem_support_right)
    exact (hrim x hx y hy h).elim
  · intro he
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    have h1:=Set.mem_toFinset.mp hx
    have h2:=Set.mem_toFinset.mp hx'
    exact hspoke he x (private_support_intersection R S S' hSS hSR hS'R x (hW x h1) (hW' x h2)) ⟨h1,h2⟩

 theorem two_root_rim_pair_disjoint (W W':OrdinaryWheel Q F H r)
    (R S S':Finset V) (x y x' y':V) (hSS:Disjoint S S')
    (hSR:Disjoint S R) (hS'R:Disjoint S' R)
    (hx:x∈R) (hy:y∈R) (hx':x'∈R) (hy':y'∈R)
    (hW:∀ v∈(ordinaryWheelRim W).support,v=x∨v=y∨v∈S)
    (hW':∀ v∈(ordinaryWheelRim W').support,v=x'∨v=y'∨v∈S')
    (hedge:s(x,y)≠s(x',y')) (hhub:ordinaryWheelHub W≠ordinaryWheelHub W'):
    Disjoint (ordinaryWheelResources W) (ordinaryWheelResources W'):=by
  apply transformer_wheel_pair_disjoint W W' R S S' hSS hSR hS'R
  · intro v hv
    rcases hW v hv with rfl|rfl|hv
    · exact Finset.mem_union_left _ hx
    · exact Finset.mem_union_left _ hy
    · exact Finset.mem_union_right _ hv
  · intro v hv
    rcases hW' v hv with rfl|rfl|hv
    · exact Finset.mem_union_left _ hx'
    · exact Finset.mem_union_left _ hy'
    · exact Finset.mem_union_right _ hv
  · intro a ha b hb hab
    have h1:a=x∨a=y:=by
      rcases hW a hab.1.mem_support_left with h|h|h
      · exact Or.inl h
      · exact Or.inr h
      · exact (Finset.disjoint_left.mp hSR h ha).elim
    have h2:b=x∨b=y:=by
      rcases hW b hab.1.mem_support_right with h|h|h
      · exact Or.inl h
      · exact Or.inr h
      · exact (Finset.disjoint_left.mp hSR h hb).elim
    have h3:a=x'∨a=y':=by
      rcases hW' a hab.2.mem_support_left with h|h|h
      · exact Or.inl h
      · exact Or.inr h
      · exact (Finset.disjoint_left.mp hS'R h ha).elim
    have h4:b=x'∨b=y':=by
      rcases hW' b hab.2.mem_support_right with h|h|h
      · exact Or.inl h
      · exact Or.inr h
      · exact (Finset.disjoint_left.mp hS'R h hb).elim
    have hEq (s t:V) (hs:a=s∨a=t) (ht:b=s∨b=t):s(a,b)=s(s,t):=by
      rcases hs with hs|hs <;> rcases ht with ht|ht
      · exact (hab.1.ne (hs.trans ht.symm)).elim
      · rw [hs,ht]
      · rw [hs,ht,Sym2.eq_swap]
      · exact (hab.1.ne (hs.trans ht.symm)).elim
    exact hedge ((hEq x y h1 h2).symm.trans (hEq x' y' h3 h4))
  · intro he;exact (hhub he).elim

 theorem one_root_wheel_pair_disjoint (W W':OrdinaryWheel Q F H r)
    (R S S':Finset V) (x y:V) (hSS:Disjoint S S')
    (hSR:Disjoint S R) (hS'R:Disjoint S' R) (hx:x∈R) (hy:y∈R)
    (hW:∀ v∈(ordinaryWheelRim W).support,v=x∨v∈S)
    (hW':∀ v∈(ordinaryWheelRim W').support,v=y∨v∈S')
    (hsp:(x,ordinaryWheelHub W)≠(y,ordinaryWheelHub W')):
    Disjoint (ordinaryWheelResources W) (ordinaryWheelResources W'):=by
  have hroot (v:V) (hv:v∈(ordinaryWheelRim W).support) (hvR:v∈R):v=x:=by
    rcases hW v hv with he|hv
    · exact he
    · exact (Finset.disjoint_left.mp hSR hv hvR).elim
  have hroot' (v:V) (hv:v∈(ordinaryWheelRim W').support) (hvR:v∈R):v=y:=by
    rcases hW' v hv with he|hv
    · exact he
    · exact (Finset.disjoint_left.mp hS'R hv hvR).elim
  apply transformer_wheel_pair_disjoint W W' R S S' hSS hSR hS'R
  · intro v hv
    rcases hW v hv with rfl|hv
    · exact Finset.mem_union_left _ hx
    · exact Finset.mem_union_right _ hv
  · intro v hv
    rcases hW' v hv with rfl|hv
    · exact Finset.mem_union_left _ hy
    · exact Finset.mem_union_right _ hv
  · intro a ha b hb hab
    exact hab.1.ne ((hroot a hab.1.mem_support_left ha).trans (hroot b hab.1.mem_support_right hb).symm)
  · intro he v hv hboth
    have hxy:x=y:=(hroot v hboth.1 hv).symm.trans (hroot' v hboth.2 hv)
    exact hsp (Prod.ext hxy he)

end Oberwolfach
