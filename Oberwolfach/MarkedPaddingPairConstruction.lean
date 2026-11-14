module

public import Oberwolfach.MarkedPaddingMaps

@[expose] public section

/-! Construct the source and image padding wheels simultaneously, then
extend both old maps. Their physical packing includes both sides, even
when the old row map identifies several marked heads. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K I:Type} [Fintype V] [Fintype U] [Fintype I]
    [DecidableEq V] [DecidableEq U] [DecidableEq I]

theorem marked_padding_pair_construction
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V)
    (b l:ℕ) (hl:1≤l) (v:I→V) (φ:V→V) (ψ:U→U) (W Z:Finset V) (B:Finset U)
    (hv:∀ i,v i∈Z∧φ (v i)∈Z) (c ch:ℝ)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hout:∀ t:Bool,∀ x,c≤((Finset.univ.filter (fun a=>
      if t then ∃ e,ktail e=x∧khead e=a else ∃ e,tail e=x∧head e=a)).card:ℝ))
    (hin:∀ i,c≤((Finset.univ.filter (fun a=>∃ e,ktail e=a∧khead e=v i)).card:ℝ)∧
      c≤((Finset.univ.filter (fun a=>∃ e,ktail e=a∧khead e=φ (v i))).card:ℝ))
    (hjoin:∀ x y,x≠y→c≤((Finset.univ.filter (fun a=>(∃ e,tail e=x∧head e=a)∧
      (∃ e,tail e=a∧head e=y))).card:ℝ))
    (hbudget:W.card+(2*(Fintype.card I:ℝ)*(l+4)+Z.card+l+5)*(2*b+1)<c)
    (hhub:∀ A C:Finset V,Disjoint A C→A.card+C.card≤l+5→
      (∀ x∈A∪C,∀ y∈A∪C,x≠y→¬PermutationClose π b x y)→
      ch≤((Finset.univ.filter (fun u=>(∀ v∈A,H₀ v u)∧∀ v∈C,HK v u)).card:ℝ))
    (hhbudget:B.card+2*Fintype.card I<ch):
    ∃ p:(Bool×I)→(Fin (l+4)↪V),∃ h:(Bool×I)↪U,
    ∃ C:(Bool×I)→MarkedWheel tail head ktail khead (l+4) π b H₀ HK,
    ∃ φ':V→V,∃ ψ':U→U,
      (∀ z∈Z,φ' z=φ z)∧(∀ z∈B,ψ' z=ψ z)∧
      (∀ i,ψ' (h (false,i))=h (true,i))∧
      (∀ i k,φ' ((C (false,i)).1.val k)=(C (true,i)).1.val k)∧
      (∀ i,(C i).2.val=h i∧h i∉B)∧
      (∀ i k,(C i).1.val k=Fin.cons (α:=fun _=>V) (if i.1 then φ (v i.2) else v i.2) (p i) k)∧
      (∀ i k,p i k∉W∧p i k∉Z∧∀ z∈Z,¬PermutationClose π b (p i k) z)∧
      (∀ i j,i≠j→Disjoint (Finset.univ.image (p i)) (Finset.univ.image (p j)))∧
      (∀ i j,∀ k k',p i k≠p j k'→¬PermutationClose π b (p i k) (p j k'))∧
      (∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j))):=by
  let vr:Bool×I→V:=fun i=>if i.1 then φ (v i.2) else v i.2
  have hvr:∀ i,vr i∈Z:=by
    rintro ⟨j,i⟩;cases j
    · exact (hv i).1
    · exact (hv i).2
  have hin':∀ i,c≤((Finset.univ.filter (fun a=>∃ e,ktail e=a∧khead e=vr i)).card:ℝ):=by
    rintro ⟨j,i⟩;cases j
    · exact (hin i).1
    · exact (hin i).2
  have hb':W.card+((Fintype.card (Bool×I):ℝ)*((l+1)+3)+Z.card+(l+1)+4)*(2*b+1)<c:=by
    simp only [Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
    convert hbudget using 1 <;> ring
  have hhb':B.card+Fintype.card (Bool×I)<ch:=by
    simpa only [Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat] using hhbudget
  obtain ⟨p,h,C,hH,hC,hav,hsep,hdis,hcross⟩:=marked_padding_wheel_families
    tail head ktail khead H₀ HK π b (l+1) (by omega) vr W Z B hvr c ch hout hin' hjoin
    (by simpa only [Nat.cast_add,Nat.cast_one] using hb') hhub hhb'
  let h₀:I↪U:={toFun:=fun i=>h (false,i),inj':=fun i j he=>congrArg Prod.snd (h.injective he)}
  obtain ⟨ψ',hψ,hψp⟩:=padding_hub_map_extension ψ h₀ (fun i=>h (true,i)) B (fun i=>(hH (false,i)).2)
  obtain ⟨φ',hφ,hφp⟩:=padding_cycle_map_extension (l+4) φ v (fun i=>p (false,i)) (fun i=>p (true,i)) Z
    (fun i=>(hv i).1) (fun i j hij=>hdis (false,i) (false,j) (fun he=>hij (congrArg Prod.snd he)))
    (fun i k=>(hav (false,i) k).2.1)
  refine ⟨p,h,C,φ',ψ',hφ,hψ,fun i=>hψp i,?_,hH,hC,hav,hdis,hcross,?_⟩
  · intro i k
    simpa only [hC,vr,Bool.false_eq_true,ite_false,ite_true] using hφp i k
  · apply marked_padding_family_packing (by omega) hp C vr p Z hvr hC (fun i k=>(hav i k).2.1) hdis
    intro i j he;apply h.injective
    simpa only [←(hH i).1,←(hH j).1] using he

end Oberwolfach
