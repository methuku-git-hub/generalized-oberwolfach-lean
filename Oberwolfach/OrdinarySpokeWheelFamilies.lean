module

public import Oberwolfach.OrdinaryOneRootPathWheels
public import Oberwolfach.TransformerWheelDisjointness

@[expose] public section

/-! The actual spoke-edge wheel families use prescribed hubs, which may
repeat. Disjointness follows from private paths and distinct old spoke
edges; hub injectivity is not assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [Fintype I]
  [DecidableEq V] [DecidableEq U] [DecidableEq I]

 theorem ordinary_spoke_wheel_families (Q F:SimpleGraph V) (H:V→U→Prop)
    (r:ℕ) (hr:3≤r) (R:Finset V) (x y:I→V) (u u':I→U)
    (p:I→(Σ a:V,Σ b:V,Q.Walk a b))
    (hroot:∀ i,x i∈R∧y i∈R) (hxy:∀ i,x i≠y i)
    (hpath:∀ i,(p i).2.2.IsPath∧(p i).2.2.length=r-2)
    (hends:∀ i,Q.Adj (x i) (p i).1∧Q.Adj (x i) (p i).2.1∧
      Q.Adj (y i) (p i).1∧Q.Adj (y i) (p i).2.1)
    (havoid:∀ i,∀ v∈(p i).2.2.support,v∉R)
    (hdis:∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset)
    (hF:∀ i,∀ v∈insert (x i) (insert (y i) (p i).2.2.support.toFinset),
      ∀ w∈insert (x i) (insert (y i) (p i).2.2.support.toFinset),¬F.Adj v w)
    (hH:∀ i,H (x i) (u i)∧H (y i) (u' i))
    (hHp:∀ i,∀ v∈(p i).2.2.support,H v (u i)∧H v (u' i))
    (hinj:Function.Injective (fun i=>(x i,u i))) (hinj':Function.Injective (fun i=>(y i,u' i))):
    ∃ W W':I→OrdinaryWheel Q F H r,
      (∀ i,ordinaryWheelHub (W i)=u i∧ordinaryWheelHub (W' i)=u' i) ∧
      (∀ i,∀ v,v∈(ordinaryWheelRim (W i)).support↔v=x i∨v∈(p i).2.2.support) ∧
      (∀ i,∀ v,v∈(ordinaryWheelRim (W' i)).support↔v=y i∨v∈(p i).2.2.support) ∧
      (∀ i j,i≠j→Disjoint (ordinaryWheelResources (W i)) (ordinaryWheelResources (W j))) ∧
      (∀ i j,i≠j→Disjoint (ordinaryWheelResources (W' i)) (ordinaryWheelResources (W' j))) ∧
      (∀ i e,
        (if Sum.inl e∈ordinaryWheelResources (W i) then (1:ℤ) else 0)-
          (if Sum.inl e∈ordinaryWheelResources (W' i) then 1 else 0)=
        (if e=s(x i,(p i).1) then 1 else 0)+(if e=s(x i,(p i).2.1) then 1 else 0)-
          (if e=s(y i,(p i).1) then 1 else 0)-(if e=s(y i,(p i).2.1) then 1 else 0)) ∧
      (∀ i v z,
        (if Sum.inr (v,z)∈ordinaryWheelResources (W i) then (1:ℤ) else 0)-
          (if Sum.inr (v,z)∈ordinaryWheelResources (W' i) then 1 else 0)=
        (if v=x i∧z=u i then 1 else 0)-(if v=y i∧z=u' i then 1 else 0)+
        (if v∈(p i).2.2.support∧z=u i then 1 else 0)-
          (if v∈(p i).2.2.support∧z=u' i then 1 else 0)):=by
  have hex (i:I):=ordinary_one_root_path_wheels Q F H r hr (x i) (y i)
    (p i).1 (p i).2.1 (u i) (u' i) (p i).2.2 (hpath i).1 (hpath i).2 (hxy i)
    (hends i).1 (hends i).2.1 (hends i).2.2.1 (hends i).2.2.2
    (fun v hv=>⟨fun he=>havoid i v hv (he.symm ▸ (hroot i).1),
      fun he=>havoid i v hv (he.symm ▸ (hroot i).2)⟩) (hF i) (hH i) (hHp i)
  choose W W' hw using hex
  have hPR (i:I):Disjoint (p i).2.2.support.toFinset R:=by
    exact Finset.disjoint_left.mpr (fun v hv=>havoid i v (List.mem_toFinset.mp hv))
  refine ⟨W,W',?_,?_,?_,?_,?_,?_,?_⟩
  · intro i;exact ⟨(hw i).1,(hw i).2.1⟩
  · intro i;exact (hw i).2.2.1
  · intro i;exact (hw i).2.2.2.1
  · intro i j hij
    apply one_root_wheel_pair_disjoint (W i) (W j) R _ _ (x i) (x j)
      (hdis i j hij) (hPR i) (hPR j) (hroot i).1 (hroot j).1
    · intro v hv;simpa only [List.mem_toFinset] using ((hw i).2.2.1 v).mp hv
    · intro v hv;simpa only [List.mem_toFinset] using ((hw j).2.2.1 v).mp hv
    · rw [(hw i).1,(hw j).1];exact fun he=>hij (hinj he)
  · intro i j hij
    apply one_root_wheel_pair_disjoint (W' i) (W' j) R _ _ (y i) (y j)
      (hdis i j hij) (hPR i) (hPR j) (hroot i).2 (hroot j).2
    · intro v hv;simpa only [List.mem_toFinset] using ((hw i).2.2.2.1 v).mp hv
    · intro v hv;simpa only [List.mem_toFinset] using ((hw j).2.2.2.1 v).mp hv
    · rw [(hw i).2.1,(hw j).2.1];exact fun he=>hij (hinj' he)
  · intro i;exact (hw i).2.2.2.2.1
  · intro i;exact (hw i).2.2.2.2.2

end Oberwolfach
