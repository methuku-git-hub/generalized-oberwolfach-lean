module

public import Oberwolfach.MarkedHostExtensionCounts

@[expose] public section

/-! Attach a fresh actual hub to a canonical cycle using the prescribed
ordinary and marked spoke classes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_cycle_fresh_hub
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (C:MarkedCycleTuple tail head ktail khead (l+4) π b) (B:Finset U) (hB:(B.card:ℝ)<ch):
    ∃ u∉B,MarkedHubCompatible H₀ HK C.val u:=by
  let A:Finset V:=Finset.univ.image (fun i:Fin (l+4)=>C.val i.succ)
  let T:Finset V:={C.val 0}
  have hd:Disjoint A T:=by
    apply Finset.disjoint_left.mpr
    intro v hv ht
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hv
    have he:C.val i.succ=C.val 0:=Finset.mem_singleton.mp ht
    exact C.property.1 i.succ 0 (Fin.succ_ne_zero _) (Or.inl he)
  have hc:A.card+T.card≤l+11:=by
    have hh: A.card≤l+4:=by
      simpa only [A,Fintype.card_fin,Finset.card_univ] using Finset.card_image_le (s:=Finset.univ) (f:=fun i:Fin (l+4)=>C.val i.succ)
    have ht:T.card=1:=Finset.card_singleton _
    omega
  have hm:∀ v∈A∪T,∃ i,C.val i=v:=by
    intro v hv
    rcases Finset.mem_union.mp hv with hv|hv
    · obtain ⟨i,_,he⟩:=Finset.mem_image.mp hv;exact ⟨i.succ,he⟩
    · exact ⟨0,(Finset.mem_singleton.mp hv).symm⟩
  have hsep:∀ v∈A∪T,∀ w∈A∪T,v≠w→¬PermutationClose π b v w:=by
    intro v hv w hw hvw
    obtain ⟨i,rfl⟩:=hm v hv
    obtain ⟨j,rfl⟩:=hm w hw
    exact C.property.1 i j (fun h=>hvw (congrArg C.val h))
  have hh:=Q.hubs A T hd hc hsep
  have hcard:B.card<(Finset.univ.filter (fun u=>(∀ x∈A,H₀ x u)∧∀ x∈T,HK x u)).card:=by
    exact_mod_cast hB.trans_le hh
  obtain ⟨u,hu,huB⟩:=Finset.exists_mem_notMem_of_card_lt_card hcard
  have hu':=(Finset.mem_filter.mp hu).2
  exact ⟨u,huB,hu'.2 _ (Finset.mem_singleton_self _),fun i=>hu'.1 _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)⟩

end Oberwolfach
