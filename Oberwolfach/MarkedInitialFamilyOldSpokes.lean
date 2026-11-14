module

public import Oberwolfach.MarkedPathFamilyOldSpokes

@[expose] public section

/-! The initial transformer families have no spoke at a retained path
label and the opposite old hub. This discharges the spoke exclusions
required when the constructed hub switches are adjoined. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 13000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S J:Type} [Fintype V] [Fintype S] [Fintype A] [Fintype J]
    [DecidableEq V] [DecidableEq U] [DecidableEq S]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {b m:ℕ} {H₀ HK:V→U→Prop}

 theorem marked_initial_family_old_spokes
    (p:S→(Fin m↪V)) (row row':S→V) (hub:S→U) (ψ:U→U) (j:S→Bool)
    (B:Finset U) (hB:∀ s,hub s∈B∧ψ (hub s)∈B) (hψ:∀ s,hub s≠ψ (hub s))
    (RC RD:A→MarkedWheel tail head ktail khead m π b H₀ HK)
    (SC SD:S→MarkedWheel tail head ktail khead m π b H₀ HK)
    (VC VD:J→MarkedWheel tail head ktail khead m π b H₀ HK)
    (hRF:∀ e,(RC e).2.val∉B∧(RD e).2.val∉B)
    (hVF:∀ z,(VC z).2.val∉B∧(VD z).2.val∉B)
    (hSC:∀ s i,(SC s).1.val i=rootedCycleOrder (markedRootOrder m (j s)) (row s) (p s) i)
    (hSD:∀ s i,(SD s).1.val i=rootedCycleOrder (markedRootOrder m (j s)) (row' s) (p s) i)
    (hSh:∀ s,(SC s).2.val=hub s∧(SD s).2.val=ψ (hub s))
    (hR:∀ s t k,p s k≠row t∧p s k≠row' t)
    (hdis:∀ s t,s≠t→Disjoint (Finset.univ.image (p s)) (Finset.univ.image (p t))):
    ∀ u v,v∈spokePathHubVertices m p hub u→
      (Sum.inr (v,ψ u):Finset V⊕(V×U))∉Finset.univ.biUnion (fun i:A⊕(S⊕J)=>
        markedWheelPhysicalResources (Sum.elim RC (Sum.elim SC VD) i))∧
      (Sum.inr (v,u):Finset V⊕(V×U))∉Finset.univ.biUnion (fun i:A⊕(S⊕J)=>
        markedWheelPhysicalResources (Sum.elim RD (Sum.elim SD VC) i)):=by
  intro u v hv
  have huB:u∈B∧ψ u∈B:=by
    obtain ⟨s,_,_⟩:=Finset.mem_biUnion.mp hv
    simpa only [s.property] using hB s.val
  have hu:u≠ψ u:=by
    obtain ⟨s,_,_⟩:=Finset.mem_biUnion.mp hv
    simpa only [s.property] using hψ s.val
  have hSCu:=marked_spoke_path_family_old_hub m p row hub id j SC hSC
    (fun s=>(hSh s).1) (fun s t k=>(hR s t k).1) hdis u v hv
  have hSDu:=marked_spoke_path_family_old_hub m p row' hub ψ j SD hSD
    (fun s=>(hSh s).2) (fun s t k=>(hR s t k).2) hdis u v hv
  constructor
  · intro he
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
    rcases i with e|s|z
    · exact (hRF e).1 (((markedWheelPhysicalResources_spoke (RC e) v (ψ u)).mp hi).1 ▸ huB.2)
    · exact hu (hSCu (ψ u) (Finset.mem_biUnion.mpr ⟨s,Finset.mem_univ _,hi⟩)).symm
    · exact (hVF z).2 (((markedWheelPhysicalResources_spoke (VD z) v (ψ u)).mp hi).1 ▸ huB.2)
  · intro he
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
    rcases i with e|s|z
    · exact (hRF e).2 (((markedWheelPhysicalResources_spoke (RD e) v u).mp hi).1 ▸ huB.1)
    · exact hu (hSDu u (Finset.mem_biUnion.mpr ⟨s,Finset.mem_univ _,hi⟩))
    · exact (hVF z).1 (((markedWheelPhysicalResources_spoke (VC z) v u).mp hi).1 ▸ huB.1)

end Oberwolfach
