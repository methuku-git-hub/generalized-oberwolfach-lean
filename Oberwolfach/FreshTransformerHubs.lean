module

public import Oberwolfach.FiniteDisjointChoices
public import Oberwolfach.OrdinaryRimEdgePairs

@[expose] public section

/-! Fresh, distinct hubs are selected after all path endpoints have
been fixed. The common-neighbour set includes the future attachment
endpoints, not merely the rim of the edge wheel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [Fintype I]
  [DecidableEq V] [DecidableEq U] [DecidableEq I]

 theorem fresh_transformer_hubs (F:SimpleGraph V) (H:V→U→Prop)
    (S:I→Finset V) (B:Finset U) (k:ℕ) (b:ℝ)
    (hS:∀ i,(S i).card≤k) (hSF:∀ i,∀ v∈S i,∀ w∈S i,¬F.Adj v w)
    (hcount:∀ T:Finset V,T.card≤k→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
      b≤((common (Finset.univ:Finset U) T (fun v=>Finset.univ.filter (H v))).card:ℝ))
    (hbudget:B.card+Fintype.card I<b):
    ∃ h:I↪U,(∀ i,h i∉B) ∧ (∀ i,∀ v∈S i,H v (h i)):=by
  have hchoose:∀ i,∀ C:Finset U,C.card≤B.card+Fintype.card I*1→
      ∃ u,(∀ v∈S i,H v u) ∧ ({u}:Finset U).card≤1 ∧ Disjoint ({u}:Finset U) C:=by
    intro i C hC
    have hCr:(C.card:ℝ)≤B.card+Fintype.card I:=by exact_mod_cast (by simpa using hC)
    have hlt:C.card<(common (Finset.univ:Finset U) (S i) (fun v=>Finset.univ.filter (H v))).card:=by
      exact_mod_cast (hCr.trans_lt hbudget).trans_le (hcount (S i) (hS i) (hSF i))
    obtain ⟨u,hu,huC⟩:=Finset.exists_mem_notMem_of_card_lt_card hlt
    refine ⟨u,?_,by simp,by simpa using huC⟩
    simpa only [common,Finset.mem_filter,Finset.mem_univ,true_and] using hu
  obtain ⟨h,hh,hd⟩:=finite_disjoint_choices (fun u:U=>({u}:Finset U))
    (fun i u=>∀ v∈S i,H v u) B 1 hchoose
  have hinj:Function.Injective h:=by
    intro i j hij
    by_contra hne
    have hn:Disjoint ({h i}:Finset U) {h j}:=hd i j hne
    simpa [hij] using hn
  exact ⟨⟨h,hinj⟩,(fun i=>by simpa using (hh i).2.2),fun i=>(hh i).1⟩

end Oberwolfach
