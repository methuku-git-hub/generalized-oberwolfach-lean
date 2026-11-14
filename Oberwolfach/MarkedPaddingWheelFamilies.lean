module

public import Oberwolfach.MarkedSpokeWheelFamilies
public import Oberwolfach.FreshMarkedTransformerHubs

@[expose] public section

/-! The padding cycles are constructed from host neighbourhood counts. Their
old marked heads need not be distinct. All other row vertices and all hubs
are chosen here, outside the prescribed forbidden sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem marked_padding_cycle_families
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (b l:ℕ) (hl:2≤l) (v:I→V) (W Z:Finset V) (hv:∀ i,v i∈Z) (c:ℝ)
    (hout:∀ t:Bool,∀ x,c≤((Finset.univ.filter (fun a=>
      if t then ∃ e,ktail e=x∧khead e=a else ∃ e,tail e=x∧head e=a)).card:ℝ))
    (hin:∀ i,c≤((Finset.univ.filter (fun a=>∃ e,ktail e=a∧khead e=v i)).card:ℝ))
    (hjoin:∀ x y,x≠y→c≤((Finset.univ.filter (fun a=>(∃ e,tail e=x∧head e=a)∧
      (∃ e,tail e=a∧head e=y))).card:ℝ))
    (hbudget:W.card+((Fintype.card I:ℝ)*(l+3)+Z.card+l+4)*(2*b+1)<c):
    ∃ p:I→(Fin (l+3)↪V),∃ C:I→MarkedCycleTuple tail head ktail khead (l+3) π b,
      (∀ i a,(C i).val a=Fin.cons (α:=fun _=>V) (v i) (p i) a)∧
      (∀ i a,p i a∉W∧p i a∉Z∧∀ z∈Z,¬PermutationClose π b (p i a) z)∧
      (∀ i,PermutationSeparated π b (p i))∧
      (∀ i k,i≠k→Disjoint (Finset.univ.image (p i)) (Finset.univ.image (p k)))∧
      ∀ i k,∀ a z,p i a≠p k z→¬PermutationClose π b (p i a) (p k z):=by
  obtain ⟨p,A,D,_,hA,_,hav,hsep,hdis,hcross⟩:=marked_spoke_wheel_families
    tail head ktail khead (fun (_:V) (_:Unit)=>True) (fun (_:V) (_:Unit)=>True)
    π b l hl v v (fun _=>()) (fun _=>()) (fun _=>true) W Z
    (fun i=>⟨hv i,hv i⟩) c (by simp)
    (fun i=>by simpa only [and_true,and_self,Bool.false_eq_true,ite_false] using hout false (v i))
    (fun i=>by simpa only [ite_true,and_true,and_self] using hin i)
    (fun _ t x=>by simpa only [and_self,ite_self,and_true] using hout t x)
    (fun _ x y hxy=>by simpa only [and_true] using hjoin x y hxy) hbudget
  refine ⟨p,fun i=>(A i).1,?_,hav,hsep,hdis,hcross⟩
  intro i a
  simpa only [rootedCycleOrder,markedRootOrder,ite_true,Equiv.refl_apply,Fin.cons] using hA i a

variable [Fintype U] [DecidableEq U]

theorem marked_padding_wheel_families
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V)
    (b l:ℕ) (hl:2≤l) (v:I→V) (W Z:Finset V) (B:Finset U)
    (hv:∀ i,v i∈Z) (c ch:ℝ)
    (hout:∀ t:Bool,∀ x,c≤((Finset.univ.filter (fun a=>
      if t then ∃ e,ktail e=x∧khead e=a else ∃ e,tail e=x∧head e=a)).card:ℝ))
    (hin:∀ i,c≤((Finset.univ.filter (fun a=>∃ e,ktail e=a∧khead e=v i)).card:ℝ))
    (hjoin:∀ x y,x≠y→c≤((Finset.univ.filter (fun a=>(∃ e,tail e=x∧head e=a)∧
      (∃ e,tail e=a∧head e=y))).card:ℝ))
    (hbudget:W.card+((Fintype.card I:ℝ)*(l+3)+Z.card+l+4)*(2*b+1)<c)
    (hhub:∀ A C:Finset V,Disjoint A C→A.card+C.card≤l+4→
      (∀ x∈A∪C,∀ y∈A∪C,x≠y→¬PermutationClose π b x y)→
      ch≤((Finset.univ.filter (fun u=>(∀ v∈A,H₀ v u)∧∀ v∈C,HK v u)).card:ℝ))
    (hhbudget:B.card+Fintype.card I<ch):
    ∃ p:I→(Fin (l+3)↪V),∃ h:I↪U,
    ∃ A:I→MarkedWheel tail head ktail khead (l+3) π b H₀ HK,
      (∀ i,(A i).2.val=h i∧h i∉B)∧
      (∀ i a,(A i).1.val a=Fin.cons (α:=fun _=>V) (v i) (p i) a)∧
      (∀ i a,p i a∉W∧p i a∉Z∧∀ z∈Z,¬PermutationClose π b (p i a) z)∧
      (∀ i,PermutationSeparated π b (p i))∧
      (∀ i k,i≠k→Disjoint (Finset.univ.image (p i)) (Finset.univ.image (p k)))∧
      ∀ i k,∀ a z,p i a≠p k z→¬PermutationClose π b (p i a) (p k z):=by
  obtain ⟨p,C,hC,hav,hsep,hdis,hcross⟩:=marked_padding_cycle_families
    tail head ktail khead π b l hl v W Z hv c hout hin hjoin hbudget
  let S₀:I→Finset V:=fun i=>Finset.univ.image (p i)
  let SK:I→Finset V:=fun i=>{v i}
  have hd:∀ i,Disjoint (S₀ i) (SK i):=by
    intro i
    apply Finset.disjoint_left.mpr
    intro x hx hk
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hx
    have he:p i a=v i:=Finset.mem_singleton.mp hk
    exact (hav i a).2.1 (he ▸ hv i)
  have hs:∀ i,(S₀ i).card+(SK i).card≤l+4:=by
    intro i
    have hh: (S₀ i).card=l+3:=by
      simp only [S₀,Finset.card_image_of_injective _ (p i).injective,Finset.card_univ,Fintype.card_fin]
    simp only [hh,SK,Finset.card_singleton]
    omega
  have hp:∀ i,∀ x∈S₀ i∪SK i,∀ y∈S₀ i∪SK i,x≠y→¬PermutationClose π b x y:=by
    intro i x hx y hy hxy
    rcases Finset.mem_union.mp hx with hx|hx <;> rcases Finset.mem_union.mp hy with hy|hy
    · obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hx
      obtain ⟨z,_,rfl⟩:=Finset.mem_image.mp hy
      exact hsep i a z (fun he=>hxy (congrArg (p i) he))
    · obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hx
      have he:y=v i:=Finset.mem_singleton.mp hy
      subst y
      exact (hav i a).2.2 _ (hv i)
    · have he:x=v i:=Finset.mem_singleton.mp hx
      subst x
      obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hy
      intro hh
      exact (hav i a).2.2 _ (hv i) ((permutationClose_symm π b _ _).mp hh)
    · have hx':x=v i:=Finset.mem_singleton.mp hx
      have hy':y=v i:=Finset.mem_singleton.mp hy
      exact False.elim (hxy (hx'.trans hy'.symm))
  obtain ⟨h,hB,hH⟩:=fresh_marked_transformer_hubs π b (l+4) H₀ HK S₀ SK B ch hd hs hp hhub hhbudget
  have hw:∀ i,MarkedHubCompatible H₀ HK (C i).val (h i):=by
    intro i
    constructor
    · rw [hC,Fin.cons_zero]
      exact (hH i).2 _ (Finset.mem_singleton_self _)
    · intro a
      rw [hC,Fin.cons_succ]
      exact (hH i).1 _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
  exact ⟨p,h,fun i=>⟨C i,⟨h i,hw i⟩⟩,fun i=>⟨rfl,hB i⟩,hC,hav,hsep,hdis,hcross⟩

end Oberwolfach
