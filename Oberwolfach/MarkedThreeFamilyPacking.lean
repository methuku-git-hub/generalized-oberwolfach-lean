module

public import Oberwolfach.MarkedVertexCrossPacking
public import Oberwolfach.ResourceDecompositions

@[expose] public section

/-! Joint packing of the three actual marked wheel families. Vertex wheels
are closed on the opposite old row set; their fixed attachment endpoints
retain the assigned-hub exclusions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S J:Type} [Fintype V] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {b:ℕ} {H₀ HK:V→U→Prop}

 theorem marked_three_family_packing (l:ℕ)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (src dst:A→V) (row:S→V) (root:J→V)
    (jr:A→Bool) (js:S→Bool) (jv:J→Bool)
    (pr:A→Fin (l+2)→V) (ps:S→Fin (l+3)→V) (pv:J→(Fin (l+3)↪V))
    (R B:Finset V)
    (RC:A→MarkedWheel tail head ktail khead (l+3) π b H₀ HK)
    (SC:S→MarkedWheel tail head ktail khead (l+3) π b H₀ HK)
    (VC:J→MarkedWheel tail head ktail khead (l+3) π b H₀ HK)
    (hRC:∀ e i,(RC e).1.val i=Fin.cons (α:=fun _=>V) (src e) (Fin.cons (dst e) (pr e))
      (canonicalMarkedRotation (if jr e then 0 else 3) i))
    (hSC:∀ s i,(SC s).1.val i=rootedCycleOrder (markedRootOrder (l+3) (js s)) (row s) (ps s) i)
    (hVC:∀ z i,(VC z).1.val i=rootedCycleOrder (markedRootOrder (l+3) (jv z)) (root z) (pv z) i)
    (hR:∀ e,src e∈R∧dst e∈R) (hS:∀ s,row s∈R) (hV:∀ z,root z∉R∪B)
    (hpR:∀ e i,pr e i∈B) (hpS:∀ s i,ps s i∈B∧ps s i∉R)
    (hpV:∀ z i,pv z i∉R∧(pv z i∈B→pv z i∈({pv z 0,pv z (Fin.last (l+2))}:Finset V)))
    (hrs:∀ e s,Disjoint (Finset.univ.image (pr e)) (Finset.univ.image (ps s)))
    (hRS:∀ e s,(RC e).2.val≠(SC s).2.val)
    (hRV:∀ e z,(pv z 0∈Finset.univ.image (pr e)∨pv z (Fin.last (l+2))∈Finset.univ.image (pr e))→
      (RC e).2.val≠(VC z).2.val)
    (hSV:∀ s z,(SC s).2.val≠(VC z).2.val)
    (hRR:∀ e f,e≠f→Disjoint (markedWheelPhysicalResources (RC e)) (markedWheelPhysicalResources (RC f)))
    (hSS:∀ s t,s≠t→Disjoint (markedWheelPhysicalResources (SC s)) (markedWheelPhysicalResources (SC t)))
    (hVV:∀ z z',z≠z'→Disjoint (markedWheelPhysicalResources (VC z)) (markedWheelPhysicalResources (VC z'))):
    let C:=Sum.elim RC (Sum.elim SC VC)
    ∀ i j:A⊕(S⊕J),i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j)):=by
  have hRCmem:∀ e i,(RC e).1.val i∈R∪B:=by
    intro e i
    have hh:(RC e).1.val i∈Finset.univ.image (RC e).1.val:=Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    rw [funext (hRC e),two_root_cycle_image] at hh
    dsimp only at hh
    rw [←hRC e i] at hh
    rcases Finset.mem_insert.mp hh with hh|hh
    · exact Finset.mem_union_left _ (hh ▸ (hR e).1)
    · rcases Finset.mem_insert.mp hh with hh|hh
      · exact Finset.mem_union_left _ (hh ▸ (hR e).2)
      · obtain ⟨k,_,hk⟩:=Finset.mem_image.mp hh
        exact Finset.mem_union_right _ (hk ▸ hpR e k)
  have hSCmem:∀ s i,(SC s).1.val i∈R∪B:=by
    intro s i
    have hh:(SC s).1.val i∈Finset.univ.image (SC s).1.val:=Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    rw [funext (hSC s),rootedCycleOrder_vertices] at hh
    rw [←hSC s i] at hh
    rcases Finset.mem_insert.mp hh with hh|hh
    · exact Finset.mem_union_left _ (hh ▸ hS s)
    · obtain ⟨k,_,hk⟩:=Finset.mem_image.mp hh
      exact Finset.mem_union_right _ (hk ▸ (hpS s k).1)
  have hcrossRS:∀ e s,Disjoint (markedWheelPhysicalResources (RC e)) (markedWheelPhysicalResources (SC s)):=by
    intro e s
    exact marked_rim_spoke_cross_packing (l+1) hp (pr e) (src e) (dst e) (jr e) (ps s) (row s) (js s)
      R (RC e) (SC s) (hRC e) (hSC s) (hR e).1 (hR e).2 (hS s)
      (fun i=>(hpS s i).2) (hrs e s) (hRS e s)
  have hcrossRV:∀ e z,Disjoint (markedWheelPhysicalResources (RC e)) (markedWheelPhysicalResources (VC z)):=by
    intro e z
    have hend:∀ k,(RC e).1.val k=pv z 0∨(RC e).1.val k=pv z (Fin.last (l+2))→(RC e).2.val≠(VC z).2.val:=by
      intro k hk
      have hh:(RC e).1.val k∈Finset.univ.image (RC e).1.val:=Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
      rw [funext (hRC e),two_root_cycle_image] at hh
      dsimp only at hh
      rw [←hRC e k] at hh
      rcases hk with hk|hk
      · rw [hk] at hh
        rcases Finset.mem_insert.mp hh with hh|hh
        · exact False.elim ((hpV z 0).1 (hh ▸ (hR e).1))
        · rcases Finset.mem_insert.mp hh with hh|hh
          · exact False.elim ((hpV z 0).1 (hh ▸ (hR e).2))
          · exact hRV e z (Or.inl hh)
      · rw [hk] at hh
        rcases Finset.mem_insert.mp hh with hh|hh
        · exact False.elim ((hpV z (Fin.last _)).1 (hh ▸ (hR e).1))
        · rcases Finset.mem_insert.mp hh with hh|hh
          · exact False.elim ((hpV z (Fin.last _)).1 (hh ▸ (hR e).2))
          · exact hRV e z (Or.inr hh)
    exact marked_vertex_cross_packing l hp (RC e) (VC z) R B (pv z) (root z) (jv z)
      (hRCmem e) (hV z) (hVC z) (fun i=>(hpV z i).1) (fun i=>(hpV z i).2)
      (fun i hi=>hend i (Or.inl hi)) (fun i hi=>hend i (Or.inr hi))
  have hcrossSV:∀ s z,Disjoint (markedWheelPhysicalResources (SC s)) (markedWheelPhysicalResources (VC z)):=by
    intro s z
    exact marked_vertex_cross_packing l hp (SC s) (VC z) R B (pv z) (root z) (jv z)
      (hSCmem s) (hV z) (hVC z) (fun i=>(hpV z i).1) (fun i=>(hpV z i).2)
      (fun _ _=>hSV s z) (fun _ _=>hSV s z)
  dsimp only
  intro i j hij
  rcases i with e|s|z <;> rcases j with f|t|w
  · exact hRR e f (fun h=>hij (congrArg Sum.inl h))
  · exact hcrossRS e t
  · exact hcrossRV e w
  · exact (hcrossRS f s).symm
  · exact hSS s t (fun h=>hij (congrArg (fun x=>Sum.inr (Sum.inl x)) h))
  · exact hcrossSV s w
  · exact (hcrossRV f z).symm
  · exact (hcrossSV t z).symm
  · exact hVV z w (fun h=>hij (congrArg (fun x=>Sum.inr (Sum.inr x)) h))

end Oberwolfach
