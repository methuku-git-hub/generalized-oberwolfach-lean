module

public import Oberwolfach.MarkedHubSwitchOldResources
public import Oberwolfach.OrdinaryHubTradeAssembly

@[expose] public section

/-! Finish a marked transformer using its actual hub switches. Opposite
root spokes and auxiliary support prove the required edge disjointness;
the signed identity then gives the two exact wheel decompositions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V U E K C:Type} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] [DecidableEq U] [DecidableEq C]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V}

 theorem marked_transformer_switch_assembly
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (R:C→Finset (Finset V⊕(V×U))) (Y Z:I→Finset V) (u u':I→U)
    (W:Finset V) (d k:ℕ) (hk:Fintype.card I≤k)
    (hY:∀ i,Disjoint (Y i) W∧(Y i).card=d) (hZ:∀ i,Z i⊆W) (hu:∀ i,u i≠u' i)
    (P N:I→Finset (Finset V⊕(V×U)))
    (hP:∀ i,HasResourceDecomposition R (P i)) (hN:∀ i,HasResourceDecomposition R (N i))
    (hdis:∀ i j,i≠j→Disjoint (P i∪N i) (P j∪N j))
    (hs:∀ i,∀ e∈P i∪N i,MarkedSwitchResource tail head ktail khead π (Y i) (Z i) (u i) (u' i) e)
    (hid:∀ i e,(if e∈P i then (1:ℤ) else 0)-(if e∈N i then 1 else 0)=
      (if e∈(Z i).image (fun v=>Sum.inr (v,u i)) then 1 else 0)-
      (if e∈(Z i).image (fun v=>Sum.inr (v,u' i)) then 1 else 0))
    (P₀ N₀ L L':Finset (Finset V⊕(V×U))) (hLL:Disjoint L L')
    (hP₀:HasResourceDecomposition R P₀) (hN₀:HasResourceDecomposition R N₀)
    (hPW:∀ e∈P₀,MarkedResourceSupported tail head ktail khead π W e)
    (hNW:∀ e∈N₀,MarkedResourceSupported tail head ktail khead π W e)
    (hsp:∀ i,∀ v∈Z i,(Sum.inr (v,u' i):Finset V⊕(V×U))∉P₀∧
      (Sum.inr (v,u i):Finset V⊕(V×U))∉N₀)
    (h₀:∀ e,(if e∈P₀ then (1:ℤ) else 0)-(if e∈N₀ then 1 else 0)=
      (if e∈L then 1 else 0)-(if e∈L' then 1 else 0)+
        ∑ i,((if e∈(Z i).image (fun v=>Sum.inr (v,u i)) then 1 else 0)-
          (if e∈(Z i).image (fun v=>Sum.inr (v,u' i)) then 1 else 0))):
    ∃ Yall:Finset V,∃ T:Finset (Finset V⊕(V×U)),
      Yall=Finset.univ.biUnion Y∧Disjoint Yall W∧Yall.card≤k*d∧
      IsResourceTransformer R L L' T∧T⊆P₀∪Finset.univ.biUnion N∧
      (∀ e∈T,MarkedResourceSupported tail head ktail khead π (W∪Yall) e)∧
      ∀ e∈T,e∉P₀→∃ i,e∈N i∧
        MarkedSwitchResource tail head ktail khead π (Y i) (Z i) (u i) (u' i) e:=by
  have hroot (i:I):=marked_switch_root_spokes (Y i) (Z i) (u i) (u' i) (hu i) (P i) (N i) (hs i) (hid i)
  have hPN:∀ i,Disjoint P₀ (N i):=by
    intro i
    apply Disjoint.symm
    apply marked_switch_side_avoids_old_resources hp (Y i) (Z i) W (u' i) (u i) (hY i).1
      (N i) P₀ hPW
    · intro e he
      exact (marked_switch_resource_swap _ _ _ _ e).mp (hs i e (Finset.mem_union_right _ he))
    · intro v hv z hz;exact (hroot i v hv z).2.mp hz
    · intro v hv;exact (hsp i v hv).1
  have hNP:∀ i,Disjoint N₀ (P i):=by
    intro i
    apply Disjoint.symm
    exact marked_switch_side_avoids_old_resources hp (Y i) (Z i) W (u i) (u' i) (hY i).1
      (P i) N₀ hNW (fun e he=>hs i e (Finset.mem_union_left _ he))
      (fun v hv z hz=>(hroot i v hv z).1.mp hz) (fun v hv=>(hsp i v hv).2)
  have hfinal:=resource_transformer_adjoin_trades R L L' P₀ N₀ P N hLL hP₀ hN₀ hP hN
    (fun i j hij=>(hdis i j hij).mono Finset.subset_union_left Finset.subset_union_left)
    (fun i j hij=>(hdis i j hij).mono Finset.subset_union_right Finset.subset_union_right)
    hPN hNP (by intro e;simpa only [hid] using h₀ e)
  let Yall:=Finset.univ.biUnion Y
  let T:=(P₀∪Finset.univ.biUnion N)\L
  have hYs (i:I):Y i⊆Yall:=fun v hv=>Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hv⟩
  refine ⟨Yall,T,rfl,?_,?_,hfinal.2,Finset.sdiff_subset,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
    exact Finset.disjoint_left.mp (hY i).1 hi hw
  · calc
      Yall.card≤∑ i,(Y i).card:=Finset.card_biUnion_le
      _=Fintype.card I*d:=by simp only [(fun i=>(hY i).2),Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]
      _≤k*d:=Nat.mul_le_mul_right d hk
  · intro e he
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp he).1 with he|he
    · exact marked_resource_support_mono Finset.subset_union_left e (hPW e he)
    · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
      apply marked_resource_support_mono (T:=Y i∪Z i) ?_ e
        (marked_switch_resource_supported _ _ _ _ e (hs i e (Finset.mem_union_right _ hi)))
      intro v hv
      rcases Finset.mem_union.mp hv with hv|hv
      · exact Finset.mem_union_right _ (hYs i hv)
      · exact Finset.mem_union_left _ (hZ i hv)
  · intro e he hn
    have hh: e∈Finset.univ.biUnion N:=(Finset.mem_union.mp (Finset.mem_sdiff.mp he).1).resolve_left hn
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hh
    exact ⟨i,hi,hs i e (Finset.mem_union_right _ hi)⟩

end Oberwolfach
