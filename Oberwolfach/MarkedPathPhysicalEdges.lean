module

public import Oberwolfach.MarkedPathParentCounts
public import Oberwolfach.MarkedPhysicalLaw

@[expose] public section

/-! Distinct physical requests for a common marked path. Roots may be
close to one another; only their inequality and their separation from the
free labels are used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def optionalSuccessor {V : Type*} (π : Equiv.Perm V) (a : Bool) (x : V) : V := if a then π x else x

theorem separated_optionalSuccessor_index {I V : Type*}
    (π : Equiv.Perm V) (b : ℕ) (hb : 1≤b) (f : I→V) (hf : PermutationSeparated π b f)
    (a c : Bool) (i j : I) (he : optionalSuccessor π a (f i)=optionalSuccessor π c (f j)) : i=j := by
  by_contra hij
  cases a <;> cases c
  · exact hf i j hij (Or.inl he)
  · exact (permutationSeparated_successor_avoid π b hb f hf j i (Ne.symm hij)) he.symm
  · exact (permutationSeparated_successor_avoid π b hb f hf i j hij) he
  · exact hf i j hij (Or.inl (π.injective he))

theorem separated_root_optionalSuccessor_ne {V : Type*} {m : ℕ}
    (π : Equiv.Perm V) (b : ℕ) (hb : 1≤b) (v : V) (f : Fin m→V)
    (hf : PermutationSeparated π b (Fin.cons v f)) (a c : Bool) (i : Fin m) :
    optionalSuccessor π a v≠optionalSuccessor π c (f i) := by
  intro he
  have hh := separated_optionalSuccessor_index π b hb (Fin.cons v f) hf a c 0 i.succ he
  exact Fin.succ_ne_zero i hh.symm

def pathInternalType (j : Bool) {m : ℕ} (i : Fin m) : Bool := decide (j=false ∧ i.val=1)

def pathPhysicalTail {V : Type*} {m : ℕ} (v v' : V) (z : Fin (m+1)→V) : Fin m⊕(Bool×Bool)→V
  | Sum.inl i=>z i.castSucc
  | Sum.inr (closing,side)=>if closing then z (Fin.last m) else if side then v' else v

def pathPhysicalHead {V : Type*} {m : ℕ} (π : Equiv.Perm V) (j : Bool)
    (v v' : V) (z : Fin (m+1)→V) : Fin m⊕(Bool×Bool)→V
  | Sum.inl i=>optionalSuccessor π (pathInternalType j i) (z i.succ)
  | Sum.inr (closing,side)=>if closing then optionalSuccessor π j (if side then v' else v) else z 0

def pathPhysicalEdge {V : Type*} {m : ℕ} (π : Equiv.Perm V) (j : Bool)
    (v v' : V) (z : Fin (m+1)→V) (i : Fin m⊕(Bool×Bool)) : Sym2 V :=
  s(pathPhysicalTail v v' z i,pathPhysicalHead π j v v' z i)

theorem pathPhysicalEdge_internal_injective {V : Type*} {m : ℕ}
    (π : Equiv.Perm V) (b : ℕ) (hb : 1≤b) (j : Bool) (v v' : V) (z : Fin (m+1)→V)
    (hz : PermutationSeparated π b z) :
    Function.Injective (fun i : Fin m=>pathPhysicalEdge π j v v' z (Sum.inl i)) := by
  intro i k he
  change s(z i.castSucc,optionalSuccessor π (pathInternalType j i) (z i.succ))=
    s(z k.castSucc,optionalSuccessor π (pathInternalType j k) (z k.succ)) at he
  rcases Sym2.eq_iff.mp he with ⟨ht,_⟩|⟨h₁,h₂⟩
  · exact Fin.castSucc_injective m (permutationSeparated_injective π b z hz ht)
  · have h₁' := separated_optionalSuccessor_index π b hb z hz false (pathInternalType j k) i.castSucc k.succ h₁
    have h₂' := separated_optionalSuccessor_index π b hb z hz (pathInternalType j i) false i.succ k.castSucc h₂
    have hv₁:=congrArg Fin.val h₁'
    have hv₂:=congrArg Fin.val h₂'
    simp only [Fin.val_castSucc,Fin.val_succ] at hv₁ hv₂
    omega

theorem pathPhysicalEdge_internal_ne_root {V : Type*} {m : ℕ}
    (π : Equiv.Perm V) (b : ℕ) (hb : 1≤b) (j : Bool) (v v' : V) (z : Fin (m+1)→V)
    (hv : PermutationSeparated π b (Fin.cons v z)) (hv' : PermutationSeparated π b (Fin.cons v' z))
    (i : Fin m) (closing side : Bool) :
    pathPhysicalEdge π j v v' z (Sum.inl i)≠pathPhysicalEdge π j v v' z (Sum.inr (closing,side)) := by
  let w := if side then v' else v
  have hw : PermutationSeparated π b (Fin.cons w z) := by dsimp [w];cases side <;> assumption
  have hroot (a c : Bool) (l : Fin (m+1)) := separated_root_optionalSuccessor_ne π b hb w z hw a c l
  intro he
  cases closing
  · change s(z i.castSucc,optionalSuccessor π (pathInternalType j i) (z i.succ))=s(w,z 0) at he
    rcases Sym2.eq_iff.mp he with ⟨ht,_⟩|⟨_,hh⟩
    · exact hroot false false i.castSucc ht.symm
    · exact hroot false (pathInternalType j i) i.succ hh.symm
  · change s(z i.castSucc,optionalSuccessor π (pathInternalType j i) (z i.succ))=
      s(z (Fin.last m),optionalSuccessor π j w) at he
    rcases Sym2.eq_iff.mp he with ⟨_,hh⟩|⟨ht,_⟩
    · exact hroot j (pathInternalType j i) i.succ hh.symm
    · exact hroot j false i.castSucc ht.symm

theorem pathPhysicalEdge_root_injective {V : Type*} {m : ℕ}
    (π : Equiv.Perm V) (b : ℕ) (hb : 1≤b) (hm : 1≤m) (j : Bool) (v v' : V) (hvv' : v≠v')
    (z : Fin (m+1)→V) (hz : PermutationSeparated π b z)
    (hv : PermutationSeparated π b (Fin.cons v z)) (hv' : PermutationSeparated π b (Fin.cons v' z)) :
    Function.Injective (fun i : Bool×Bool=>pathPhysicalEdge π j v v' z (Sum.inr i)) := by
  have hside : Function.Injective (fun a : Bool=>if a then v' else v) := by
    intro a c he;cases a <;> cases c <;> simp_all
  have hsucc : Function.Injective (optionalSuccessor π j) := by
    cases j
    · exact Function.injective_id
    · exact π.injective
  have hne : z 0≠z (Fin.last m) := by
    intro he
    have hh:=congrArg Fin.val (permutationSeparated_injective π b z hz he)
    simp only [Fin.val_zero,Fin.val_last] at hh
    omega
  have hroot (side a c : Bool) (i : Fin (m+1)) :
      optionalSuccessor π a (if side then v' else v)≠optionalSuccessor π c (z i) := by
    apply separated_root_optionalSuccessor_ne π b hb _ z _ a c i
    cases side <;> assumption
  rintro ⟨a,c⟩ ⟨a',c'⟩ he
  cases a <;> cases a'
  · change s((if c then v' else v),z 0)=s((if c' then v' else v),z 0) at he
    rcases Sym2.eq_iff.mp he with ⟨hr,_⟩|⟨hr,_⟩
    · exact congrArg (fun a=>(false,a)) (hside hr)
    · exact (hroot c false false 0 hr).elim
  · change s((if c then v' else v),z 0)=s(z (Fin.last m),optionalSuccessor π j (if c' then v' else v)) at he
    rcases Sym2.eq_iff.mp he with ⟨hr,_⟩|⟨_,hh⟩
    · exact (hroot c false false (Fin.last m) hr).elim
    · exact (hne hh).elim
  · change s(z (Fin.last m),optionalSuccessor π j (if c then v' else v))=s((if c' then v' else v),z 0) at he
    rcases Sym2.eq_iff.mp he with ⟨hr,_⟩|⟨hh,_⟩
    · exact (hroot c' false false (Fin.last m) hr.symm).elim
    · exact (hne hh.symm).elim
  · change s(z (Fin.last m),optionalSuccessor π j (if c then v' else v))=
      s(z (Fin.last m),optionalSuccessor π j (if c' then v' else v)) at he
    rcases Sym2.eq_iff.mp he with ⟨_,hh⟩|⟨hh,_⟩
    · exact congrArg (fun a=>(true,a)) (hside (hsucc hh))
    · exact (hroot c' j false (Fin.last m) hh.symm).elim

theorem pathPhysicalEdge_injective {V : Type*} {m : ℕ}
    (π : Equiv.Perm V) (b : ℕ) (hb : 1≤b) (hm : 1≤m) (j : Bool) (v v' : V) (hvv' : v≠v')
    (z : Fin (m+1)→V) (hz : PermutationSeparated π b z)
    (hv : PermutationSeparated π b (Fin.cons v z)) (hv' : PermutationSeparated π b (Fin.cons v' z)) :
    Function.Injective (pathPhysicalEdge π j v v' z) := by
  intro i k he
  cases i with
  | inl i=>cases k with
    | inl k=>exact congrArg Sum.inl (pathPhysicalEdge_internal_injective π b hb j v v' z hz he)
    | inr k=>exact (pathPhysicalEdge_internal_ne_root π b hb j v v' z hv hv' i k.1 k.2 he).elim
  | inr i=>cases k with
    | inl k=>exact (pathPhysicalEdge_internal_ne_root π b hb j v v' z hv hv' k i.1 i.2 he.symm).elim
    | inr k=>exact congrArg Sum.inr (pathPhysicalEdge_root_injective π b hb hm j v v' hvv' z hz hv hv' he)

end Oberwolfach
