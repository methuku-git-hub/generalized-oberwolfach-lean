module

public import Oberwolfach.RootComparisonHosts
public import Oberwolfach.OrdinaryWheelFamilies

@[expose] public section

/-! Finite row-root packings and exact physical images of indexed wheels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [Fintype I] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

structure OrdinaryRowCover (M:Finset (OrdinaryWheel Q F H r)) (x:V) (A:Finset V) (K:ℕ) : Prop where
  disjoint : ∀ W∈M,∀ Z∈M,W≠Z → Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)
  support : ∀ W∈M,∀ a∈(ordinaryWheelRim W).support,a=x∨a∈A
  rims : ∀ a,(ordinaryWheelRimGraph M).Adj x a ↔ Q.Adj x a
  spokes : ∀ u,ordinaryPackingSpokes M x u ↔ H x u
  rimDegree : ∀ a,a≠x → (ordinaryWheelRimGraph M).degree a≤2*(K+1)
  rowDegree : ∀ a,a≠x → (Finset.univ.filter (ordinaryPackingSpokes M a)).card≤K+1
  columnDegree : ∀ u,(Finset.univ.filter (fun a=>ordinaryPackingSpokes M a u)).card≤r

theorem ordinary_family_image_rim (C:I→OrdinaryWheel Q F H r) :
    ordinaryWheelRimGraph (Finset.univ.image C)=wheelFamilyRim C := by
  ext a b
  simp only [ordinaryWheelRimGraph,wheelFamilyRim,SimpleGraph.iSup_adj,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨W,⟨i,rfl⟩,hab⟩;exact ⟨i,hab⟩
  · rintro ⟨i,hab⟩;exact ⟨C i,⟨i,rfl⟩,hab⟩

theorem ordinary_family_image_spokes (C:I→OrdinaryWheel Q F H r) :
    ordinaryPackingSpokes (Finset.univ.image C)=wheelFamilySpokes C := by
  funext a u
  apply propext
  simp only [ordinaryPackingSpokes,wheelFamilySpokes,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨W,⟨i,rfl⟩,h⟩;exact ⟨i,h⟩
  · rintro ⟨i,h⟩;exact ⟨C i,⟨i,rfl⟩,h⟩

theorem ordinaryRowCover_of_family (C:I→OrdinaryWheel Q F H r) (x:V) (A:Finset V) (K:ℕ)
    (hsupport:∀ i,∀ a∈(ordinaryWheelRim (C i)).support,a=x∨a∈A)
    (hdis:∀ i j,i≠j → Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j)))
    (hrim:∀ a,(wheelFamilyRim C).Adj x a ↔ Q.Adj x a)
    (hspoke:∀ u,wheelFamilySpokes C x u ↔ H x u)
    (hdeg:∀ a,a≠x → (wheelFamilyRim C).degree a≤2*(K+1))
    (hrow:∀ a,a≠x → (Finset.univ.filter (fun u=>wheelFamilySpokes C a u)).card≤K+1)
    (hcol:∀ u,(Finset.univ.filter (fun a=>wheelFamilySpokes C a u)).card≤r) :
    OrdinaryRowCover (Finset.univ.image C) x A K := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro W hW Z hZ hne
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hW
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hZ
    exact hdis i j (fun he=>hne (congrArg C he))
  · intro W hW a ha
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hW
    exact hsupport i a ha
  · simpa only [ordinary_family_image_rim] using hrim
  · simpa only [ordinary_family_image_spokes] using hspoke
  · intro a ha
    have he:=ordinary_family_image_rim C
    have hh:=hdeg a ha
    convert hh using 1 <;> rw [he]
  · simpa only [ordinary_family_image_spokes] using hrow
  · simpa only [ordinary_family_image_spokes] using hcol

theorem ordinaryPackingSpokes_biUnion {n:ℕ} (M:Fin n→Finset (OrdinaryWheel Q F H r)) (a:V) (u:U) :
    ordinaryPackingSpokes (Finset.univ.biUnion M) a u ↔ ∃ i,ordinaryPackingSpokes (M i) a u := by
  simp only [ordinaryPackingSpokes,Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨W,⟨i,hi⟩,h⟩;exact ⟨i,W,hi,h⟩
  · rintro ⟨i,W,hi,h⟩;exact ⟨W,⟨i,hi⟩,h⟩

theorem relation_iUnion_degree_bound {X J:Type} [Fintype X] [Fintype J]
    (P:J→X→Prop) (D:ℕ) (hP:∀ j,(Finset.univ.filter (P j)).card≤D) :
    (Finset.univ.filter (fun x=>∃ j,P j x)).card≤Fintype.card J*D := by
  classical
  have he:Finset.univ.filter (fun x=>∃ j,P j x)=Finset.univ.biUnion (fun j=>Finset.univ.filter (P j)):=by
    ext x;simp
  rw [he]
  calc
    _ ≤ ∑ j,(Finset.univ.filter (P j)).card:=Finset.card_biUnion_le
    _ ≤ ∑ _j:J,D:=Finset.sum_le_sum (fun j _=>hP j)
    _ = _:=by simp

end Oberwolfach
