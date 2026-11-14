module

public import Oberwolfach.FiniteDisjointChoices
public import Oberwolfach.MarkedWheels

@[expose] public section

/-! Choose actual distinct typed hubs after fixing the shared rim paths
and their future attachment neighbours. The two spoke classes are kept
separate in the candidate intersection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [Fintype I]
  [DecidableEq V] [DecidableEq U] [DecidableEq I]

 theorem fresh_marked_transformer_hubs (π:Equiv.Perm V) (b k:ℕ)
    (H₀ HK:V→U→Prop) (S₀ SK:I→Finset V) (B:Finset U) (c:ℝ)
    (hdis:∀ i,Disjoint (S₀ i) (SK i)) (hsize:∀ i,(S₀ i).card+(SK i).card≤k)
    (hsep:∀ i,∀ x∈S₀ i∪SK i,∀ y∈S₀ i∪SK i,x≠y→¬PermutationClose π b x y)
    (hcount:∀ A C:Finset V,Disjoint A C→A.card+C.card≤k→
      (∀ x∈A∪C,∀ y∈A∪C,x≠y→¬PermutationClose π b x y)→
      c≤((Finset.univ.filter (fun u=>(∀ v∈A,H₀ v u)∧∀ v∈C,HK v u)).card:ℝ))
    (hbudget:B.card+Fintype.card I<c):
    ∃ h:I↪U,(∀ i,h i∉B)∧∀ i,(∀ v∈S₀ i,H₀ v (h i))∧∀ v∈SK i,HK v (h i):=by
  let Good:I→U→Prop:=fun i u=>(∀ v∈S₀ i,H₀ v u)∧∀ v∈SK i,HK v u
  have hc:∀ i,∀ C:Finset U,C.card≤B.card+Fintype.card I*1→
      ∃ u,Good i u∧({u}:Finset U).card≤1∧Disjoint ({u}:Finset U) C:=by
    intro i C hC
    have hr:(C.card:ℝ)≤B.card+Fintype.card I:=by exact_mod_cast (by simpa using hC)
    have hl:C.card<(Finset.univ.filter (Good i)).card:=by
      exact_mod_cast (hr.trans_lt hbudget).trans_le (hcount (S₀ i) (SK i) (hdis i) (hsize i) (hsep i))
    obtain ⟨u,hu,huC⟩:=Finset.exists_mem_notMem_of_card_lt_card hl
    exact ⟨u,(Finset.mem_filter.mp hu).2,by simp,by simpa using huC⟩
  obtain ⟨h,hh,hd⟩:=finite_disjoint_choices (fun u:U=>({u}:Finset U)) Good B 1 hc
  have hi:Function.Injective h:=by
    intro i j he
    by_contra hij
    have hx:=hd i j hij
    simpa [he] using hx
  exact ⟨⟨h,hi⟩,fun i=>by simpa using (hh i).2.2,fun i=>(hh i).1⟩

 theorem marked_cycle_pair_at_typed_hub {E K:Type}
    {tail head:E→V} {ktail khead:K→V} {m:ℕ} {π:Equiv.Perm V} {b:ℕ}
    (H₀ HK:V→U→Prop) (C D:MarkedCycleTuple tail head ktail khead m π b)
    (S₀ SK:Finset V) (u:U)
    (hC:∀ i:Fin m,C.val i.succ∈S₀) (hD:∀ i:Fin m,D.val i.succ∈S₀)
    (hCK:C.val 0∈SK) (hDK:D.val 0∈SK)
    (h₀:∀ v∈S₀,H₀ v u) (hK:∀ v∈SK,HK v u):
    ∃ A B:MarkedWheel tail head ktail khead m π b H₀ HK,
      A.1=C∧B.1=D∧A.2.val=u∧B.2.val=u:=by
  exact ⟨⟨C,⟨u,hK _ hCK,fun i=>h₀ _ (hC i)⟩⟩,
    ⟨D,⟨u,hK _ hDK,fun i=>h₀ _ (hD i)⟩⟩,rfl,rfl,rfl,rfl⟩

end Oberwolfach
