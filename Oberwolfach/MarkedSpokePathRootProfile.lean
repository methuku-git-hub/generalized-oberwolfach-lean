module

public import Oberwolfach.RootFirstCommonPaths
public import Mathlib.Data.Finset.Card

@[expose] public section

/-! The exact root profile contributed by all spoke paths at one old hub.
Each ordinary root contributes one marked free vertex; a marked root
contributes none. The original hub divisibility gives the required (1,m)
ratio for their union. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype I] [DecidableEq I] [DecidableEq V]

 theorem rootFirstSpokeType_free_succ (m:ℕ) (hm:3≤m) (j:Bool) (k:Fin m):
    rootFirstSpokeType m j k.succ=decide (j=false∧k.val=2):=by
  cases j
  · have he:(k.succ:Fin (m+1))=3↔k.val=2:=by
      constructor
      · intro hh
        have hh':=congrArg Fin.val hh
        change k.val+1=3%(m+1) at hh'
        rw [Nat.mod_eq_of_lt (by omega)] at hh'
        omega
      · intro hh
        apply Fin.ext
        change k.val+1=3%(m+1)
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
    simp only [rootFirstSpokeType,Bool.false_eq_true,ite_false,true_and,he]
  · simp [rootFirstSpokeType]

 theorem marked_spoke_path_root_profile (m:ℕ) (hm:3≤m)
    (p:I→(Fin m↪V)) (j:I→Bool)
    (hdis:∀ i k,i≠k→Disjoint (Finset.univ.image (p i)) (Finset.univ.image (p k)))
    (hbalance:(Finset.univ.filter (fun i=>j i=false)).card=
      m*(Finset.univ.filter (fun i=>j i=true)).card)
    (H₀ HK:V→U→Prop) (u u':U) (htypes:∀ v,HK v u→¬H₀ v u)
    (hsp:∀ i k,if rootFirstSpokeType m (j i) k.succ then
      HK (p i k) u∧HK (p i k) u' else H₀ (p i k) u∧H₀ (p i k) u'):
    let Z:=Finset.univ.biUnion (fun i=>Finset.univ.image (p i))
    ∃ ZK ZO:Finset V,ZK∪ZO=Z∧Disjoint ZK ZO∧ZO.card=m*ZK.card∧
      ZK.card=(Finset.univ.filter (fun i=>j i=false)).card∧Z.card=m*Fintype.card I∧
      (∀ v∈Z,v∈ZK↔HK v u∧HK v u')∧(∀ v∈Z,v∈ZO↔H₀ v u∧H₀ v u'):=by
  intro Z
  let f:I×Fin m→V:=fun z=>p z.1 z.2
  have hf:Function.Injective f:=by
    rintro ⟨i,a⟩ ⟨k,c⟩ he
    have hik:i=k:=by
      by_contra hne
      exact Finset.disjoint_left.mp (hdis i k hne)
        (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
        (Finset.mem_image.mpr ⟨c,Finset.mem_univ _,he.symm⟩)
    subst k
    exact Prod.ext rfl ((p i).injective he)
  have hZ:Z=Finset.univ.image f:=by
    ext v
    simp only [Z,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_image]
    constructor
    · rintro ⟨i,k,hk⟩
      exact ⟨(i,k),hk⟩
    · rintro ⟨⟨i,k⟩,hk⟩
      exact ⟨i,k,hk⟩
  let O:=Finset.univ.filter (fun i=>j i=false)
  let K:=Finset.univ.filter (fun i=>j i=true)
  let z:Fin m:=⟨2,by omega⟩
  let ZK:=O.image (fun i=>p i z)
  let ZO:=Z\ZK
  have hKZ:ZK⊆Z:=by
    intro v hv
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hv
    rw [hZ]
    exact Finset.mem_image.mpr ⟨(i,z),Finset.mem_univ _,rfl⟩
  have hmem (i:I) (k:Fin m):p i k∈ZK↔j i=false∧k.val=2:=by
    constructor
    · intro hh
      obtain ⟨i',hi',he⟩:=Finset.mem_image.mp hh
      have he':(i',z)=(i,k):=hf he
      have hie:i'=i:=congrArg Prod.fst he'
      have hke:z=k:=congrArg Prod.snd he'
      exact ⟨hie ▸ (Finset.mem_filter.mp hi').2,by rw [←hke]⟩
    · rintro ⟨hi,hk⟩
      have hk':z=k:=Fin.ext hk.symm
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,congrArg (p i) hk'⟩
  have hKc:ZK.card=O.card:=by
    apply Finset.card_image_of_injective
    intro i k he
    have hh:(i,z)=(k,z):=hf he
    exact congrArg Prod.fst hh
  have hZc:Z.card=m*Fintype.card I:=by
    rw [hZ,Finset.card_image_of_injective _ hf,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Nat.mul_comm]
  have hIK:Fintype.card I=O.card+K.card:=by
    have hd:Disjoint O K:=by
      apply Finset.disjoint_left.mpr
      intro i hi hk
      have ho: j i=false:=(Finset.mem_filter.mp hi).2
      have hm: j i=true:=(Finset.mem_filter.mp hk).2
      exact Bool.false_ne_true (ho.symm.trans hm)
    have he:O∪K=Finset.univ:=by
      ext i
      simp only [O,K,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
      cases j i <;> simp
    have hh:=congrArg Finset.card he
    rw [Finset.card_union_of_disjoint hd,Finset.card_univ] at hh
    exact hh.symm
  have hOc:ZO.card=m*ZK.card:=by
    have hh:ZO.card=Z.card-ZK.card:=Finset.card_sdiff_of_subset hKZ
    have hk:ZK.card≤Z.card:=Finset.card_le_card hKZ
    have hbal:O.card=m*K.card:=hbalance
    rw [hh,hKc,hZc,hIK,Nat.mul_add,←hbal]
    omega
  have hclass:∀ v∈Z,v∈ZK↔HK v u∧HK v u':=by
    intro v hv
    rw [hZ] at hv
    obtain ⟨⟨i,k⟩,_,rfl⟩:=Finset.mem_image.mp hv
    change p i k∈ZK↔_
    rw [hmem]
    have hs:=hsp i k
    rw [rootFirstSpokeType_free_succ m hm] at hs
    by_cases hj:j i=false∧k.val=2
    · simpa [hj,f] using hs
    · simp [hj,f] at hs ⊢
      exact fun h _=>htypes _ h hs.1
  have hordinary:∀ v∈Z,v∈ZO↔H₀ v u∧H₀ v u':=by
    intro v hv
    have he:v∈ZO↔v∉ZK:=by simp only [ZO,Finset.mem_sdiff,hv,true_and]
    rw [he]
    rw [hZ] at hv
    obtain ⟨⟨i,k⟩,_,rfl⟩:=Finset.mem_image.mp hv
    change p i k∉ZK↔_
    rw [hmem]
    have hs:=hsp i k
    rw [rootFirstSpokeType_free_succ m hm] at hs
    by_cases hj:j i=false∧k.val=2
    · simp [hj,f] at hs ⊢
      exact fun h _=>htypes _ hs.1 h
    · simpa [hj,f] using hs
  refine ⟨ZK,ZO,?_,?_,hOc,hKc,hZc,hclass,hordinary⟩
  · exact Finset.union_sdiff_of_subset hKZ
  · apply Finset.disjoint_left.mpr
    intro v hv hh
    exact (Finset.mem_sdiff.mp hh).2 hv

end Oberwolfach
