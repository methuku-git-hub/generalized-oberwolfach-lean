module

public import Oberwolfach.OrdinaryVertexWheelPairs
public import Oberwolfach.TransformerWheelDisjointness
public import Oberwolfach.OrdinaryWheelFamilies

@[expose] public section

/-! Physical disjointness of the constructed vertex-wheel pairs. Their
fixed endpoints are disjoint, their internal vertices avoid every fixed
endpoint and old root, and their root spokes are distinct. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [Fintype I]
  [DecidableEq V] [DecidableEq U] [DecidableEq I]

 theorem ordinary_vertex_wheel_packing (Q F:SimpleGraph V) (H:V→U→Prop) (r:ℕ)
    (x y a b:I→V) (u:I→U)
    (D:∀ i,OrdinaryVertexWheelPair Q F H r (x i) (y i) (a i) (b i) (u i))
    (R W:Finset V) (hRW:R⊆W) (hx:∀ i,x i∈R) (hy:∀ i,y i∈R)
    (ha:∀ i,a i∈W∧a i∉R) (hb:∀ i,b i∈W∧b i∉R)
    (hend:∀ i j,i≠j→Disjoint ({a i,b i}:Finset V) {a j,b j})
    (havoid:∀ i,∀ v∈rootWheelInternal (D i).first (x i) (a i) (b i),v∉W)
    (hint:∀ i j,i≠j→Disjoint (rootWheelInternal (D i).first (x i) (a i) (b i))
      (rootWheelInternal (D j).first (x j) (a j) (b j)))
    (hxu:Function.Injective (fun i=>(x i,u i))) (hyu:Function.Injective (fun i=>(y i,u i))):
    (∀ i j,i≠j→Disjoint (ordinaryWheelResources (D i).first) (ordinaryWheelResources (D j).first)) ∧
    (∀ i j,i≠j→Disjoint (ordinaryWheelResources (D i).second) (ordinaryWheelResources (D j).second)) ∧
    HasOrdinaryWheelDecomposition (wheelFamilyRim (fun i=>(D i).first)) (wheelFamilySpokes (fun i=>(D i).first)) r ∧
    HasOrdinaryWheelDecomposition (wheelFamilyRim (fun i=>(D i).second)) (wheelFamilySpokes (fun i=>(D i).second)) r:=by
  let S:I→Finset V:=fun i=>(ordinaryWheelRim (D i).first).support.toFinset\{x i}
  have hS (i:I) (v:V):v∈S i↔v∈(ordinaryWheelRim (D i).first).support∧v≠x i:=by
    simp only [S,Finset.mem_sdiff,Finset.mem_singleton,Set.mem_toFinset]
  have hsplit (i:I) (v:V) (hv:v∈S i):
      v∈({a i,b i}:Finset V)∨v∈rootWheelInternal (D i).first (x i) (a i) (b i):=by
    by_cases he:v∈({a i,b i}:Finset V)
    · exact Or.inl he
    · apply Or.inr
      have hi:=(hS i v).mp hv
      simp only [rootWheelInternal,Finset.mem_sdiff,Set.mem_toFinset,Finset.mem_insert,Finset.mem_singleton]
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at he
      exact ⟨hi.1,by tauto⟩
  have hEndW (i:I) (v:V) (hv:v∈({a i,b i}:Finset V)):v∈W∧v∉R:=by
    rcases Finset.mem_insert.mp hv with he|he
    · rw [he];exact ha i
    · rw [Finset.mem_singleton.mp he];exact hb i
  have hSR (i:I):Disjoint (S i) R:=by
    apply Finset.disjoint_left.mpr
    intro v hv hvR
    rcases hsplit i v hv with he|hi
    · exact (hEndW i v he).2 hvR
    · exact havoid i v hi (hRW hvR)
  have hSS (i j:I) (hij:i≠j):Disjoint (S i) (S j):=by
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    rcases hsplit i v hv with he|hi <;> rcases hsplit j v hv' with he'|hi'
    · exact Finset.disjoint_left.mp (hend i j hij) he he'
    · exact havoid j v hi' (hEndW i v he).1
    · exact havoid i v hi (hEndW j v he').1
    · exact Finset.disjoint_left.mp (hint i j hij) hi hi'
  have hfirst (i:I) (v:V) (hv:v∈(ordinaryWheelRim (D i).first).support):v=x i∨v∈S i:=by
    by_cases he:v=x i
    · exact Or.inl he
    · exact Or.inr ((hS i v).mpr ⟨hv,he⟩)
  have hsecond (i:I) (v:V) (hv:v∈(ordinaryWheelRim (D i).second).support):v=y i∨v∈S i:=by
    rcases ((D i).second_support v).mp hv with he|hv
    · exact Or.inl he
    · exact Or.inr ((hS i v).mpr hv)
  have hfirstDis (i j:I) (hij:i≠j):Disjoint (ordinaryWheelResources (D i).first) (ordinaryWheelResources (D j).first):=by
    apply one_root_wheel_pair_disjoint (D i).first (D j).first R (S i) (S j) (x i) (x j)
      (hSS i j hij) (hSR i) (hSR j) (hx i) (hx j) (hfirst i) (hfirst j)
    rw [(D i).first_hub,(D j).first_hub]
    exact fun he=>hij (hxu he)
  have hsecondDis (i j:I) (hij:i≠j):Disjoint (ordinaryWheelResources (D i).second) (ordinaryWheelResources (D j).second):=by
    apply one_root_wheel_pair_disjoint (D i).second (D j).second R (S i) (S j) (y i) (y j)
      (hSS i j hij) (hSR i) (hSR j) (hy i) (hy j) (hsecond i) (hsecond j)
    rw [(D i).second_hub,(D j).second_hub]
    exact fun he=>hij (hyu he)
  exact ⟨hfirstDis,hsecondDis,wheelFamily_decomposition (fun i=>(D i).first) hfirstDis,
    wheelFamily_decomposition (fun i=>(D i).second) hsecondDis⟩

end Oberwolfach
