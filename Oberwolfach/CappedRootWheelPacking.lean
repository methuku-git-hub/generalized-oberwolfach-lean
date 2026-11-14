module

public import Oberwolfach.SparsePathDeletion
public import Oberwolfach.RootWheelCoverage

@[expose] public section

/-! Successive wheel completion at one row root. The internal-use cap
controls the deleted rim degree away from that root. No factor or wheel
existence statement is left as an assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem capped_ordinary_root_wheels (Q F:SimpleGraph V) (H:V→U→Prop)
    (r N K:ℕ) (hr:4≤r) (hK:0<K) (x:V) (v w:Fin N→V) (u:Fin N→U)
    (hu:Function.Injective u) (hvw:∀ i,v i≠w i)
    (hpair:∀ i j,i≠j → Disjoint ({v i,w i}:Finset V) {v j,w j})
    (A:Fin N→Finset V) (hxA:∀ i,x∉A i)
    (hxv:∀ i,Q.Adj x (v i)) (hxw:∀ i,Q.Adj x (w i))
    (hFroot:∀ i,∀ a∈({x,v i,w i}:Finset V),∀ b∈({x,v i,w i}:Finset V),¬F.Adj a b)
    (hHroot:∀ i,H x (u i)∧H (v i) (u i)∧H (w i) (u i))
    (hHA:∀ i,∀ a∈A i,H a (u i))
    (L b:ℝ) (hL:0≤L) (hF:∀ a,(F.degree a:ℝ)≤L)
    (hcount:∀ i,∀ a,a≠x → ∀ b',b'≠x →
      b≤((A i∩Q.neighborFinset a∩Q.neighborFinset b').card:ℝ))
    (hbudget:(N*r:ℕ)/(K:ℝ)+((r:ℝ)+3)*(L+1)+4*(K+1)<b) :
    ∃ C:Fin N→OrdinaryWheel Q F H r,
      (∀ i,ordinaryWheelHub (C i)=u i ∧ (ordinaryWheelRim (C i)).Adj x (v i) ∧
        (ordinaryWheelRim (C i)).Adj x (w i) ∧
        (∀ a∈(ordinaryWheelRim (C i)).support,a∈({x,v i,w i}:Finset V) ∨ a∈A i)) ∧
      (∀ i j,i≠j → Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j))) ∧
      (∀ a,rootWheelInternalLoad C x v w a≤K) ∧
      (∀ a,a≠x → (wheelFamilyRim C).degree a≤2*(K+1)) ∧
      (∀ a,(wheelFamilyRim C).Adj x a ↔ ∃ i,a=v i∨a=w i) ∧
      (∀ b',wheelFamilySpokes C x b' ↔ ∃ i,u i=b') ∧
      (∀ a,a≠x → (Finset.univ.filter (fun b'=>wheelFamilySpokes C a b')).card≤K+1) ∧
      (∀ b',(Finset.univ.filter (fun a=>wheelFamilySpokes C a b')).card≤r) := by
  let Good (i:Fin N) (C:OrdinaryWheel Q F H r):=
    ordinaryWheelHub C=u i ∧ (ordinaryWheelRim C).Adj x (v i) ∧
      (ordinaryWheelRim C).Adj x (w i) ∧
      ∀ a∈(ordinaryWheelRim C).support,a∈({x,v i,w i}:Finset V) ∨ a∈A i
  have hprefix : ∀ k:ℕ,∀ hk:k≤N,∃ C:Fin k→OrdinaryWheel Q F H r,
      (∀ i,Good ⟨i.val,lt_of_lt_of_le i.isLt hk⟩ (C i)) ∧
      (∀ i j,i≠j → Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j))) ∧
      ∀ a,rootWheelInternalLoad C x (fun i=>v ⟨i.val,lt_of_lt_of_le i.isLt hk⟩)
        (fun i=>w ⟨i.val,lt_of_lt_of_le i.isLt hk⟩) a≤K:=by
    intro k
    induction k with
    | zero =>
      intro hk
      refine ⟨Fin.elim0,fun i=>Fin.elim0 i,fun i=>Fin.elim0 i,?_⟩
      intro a
      simp [rootWheelInternalLoad]
    | succ k ih =>
      intro hk
      have hkN:k≤N:=by omega
      obtain ⟨C,hG,hdis,hcap⟩:=ih hkN
      let e:Fin k↪Fin N:=⟨fun j=>⟨j.val,lt_of_lt_of_le j.isLt hkN⟩,by intro a b h;exact Fin.ext (congrArg (fun z:Fin N=>z.val) h)⟩
      let i:Fin N:=⟨k,by omega⟩
      let vv:Fin k→V:=fun j=>v (e j)
      let ww:Fin k→V:=fun j=>w (e j)
      let D:=wheelFamilyRim C
      let S:=Finset.univ.filter (fun a=>K≤rootWheelInternalLoad C x vv ww a)
      have hcap':∀ a,rootWheelInternalLoad C x vv ww a≤K:=hcap
      have hend (a:V):(Finset.univ.filter (fun j=>a=vv j∨a=ww j)).card≤1:=
        disjoint_pairs_endpoint_count vv ww (fun a b hab=>hpair (e a) (e b) (fun he=>hab (e.injective he))) a
      have hD (a:V) (hax:a≠x):(D.degree a:ℝ)≤2*(K+1):=by
        exact_mod_cast rootWheelFamily_degree C x vv ww K hend hcap' a hax
      have hScard:(S.card:ℝ)≤(N*r:ℕ)/(K:ℝ):=by
        apply (le_div_iff₀ (Nat.cast_pos.mpr hK)).mpr
        have hh:K*S.card≤N*r:=by
          have hh:=rootWheelInternal_saturated C x vv ww K
          simp only [Fintype.card_fin] at hh
          exact hh.trans (Nat.mul_le_mul_right r hkN)
        exact_mod_cast (by simpa only [Nat.mul_comm] using hh)
      have hnew (a:V) (ha:a∈({v i,w i}:Finset V)):¬D.Adj x a:=by
        intro hDa
        obtain ⟨j,hj⟩:=SimpleGraph.iSup_adj.mp hDa
        have hne:e j≠i:=by intro he;have he':=congrArg Fin.val he;have hj':=j.isLt;dsimp [e,i] at he';omega
        have hn:=ordinaryWheel_root_neighbors (C j) x (vv j) (ww j) (hvw (e j)) (hG j).2.1 (hG j).2.2.1
        have haj:a∈({vv j,ww j}:Finset V):=by
          rw [←hn];exact ((ordinaryWheelRim (C j)).mem_neighborFinset x a).mpr hj
        exact Finset.disjoint_left.mp (hpair (e j) i hne) haj ha
      obtain ⟨B,hBu,hBv,hBw,hBD,hBA⟩:=ordinary_root_wheel_after_local_deletion Q D F H (A i) S x (v i) (w i) (u i)
        (hxA i) (hvw i) (hxv i) (hxw i) (hnew _ (by simp)) (hnew _ (by simp))
        (hFroot i) (hHroot i) (hHA i) r hr L (2*(K+1)) b hL hF hD (hcount i)
        (by linarith only [hScard,hbudget])
      have hB:Good i B:=⟨hBu,hBv,hBw,fun a ha=>(hBA a ha).imp_right And.left⟩
      have hcross (j:Fin k):Disjoint (ordinaryWheelResources (C j)) (ordinaryWheelResources B):=by
        apply Finset.disjoint_left.mpr
        intro z hz hzB
        cases z with
        | inl edge =>
          rw [ordinaryWheelResources_rim] at hz hzB
          induction edge using Sym2.inductionOn with
          | _ a b' =>
            have hDab:D.Adj a b':=SimpleGraph.iSup_adj.mpr ⟨j,hz⟩
            exact disjoint_graphs_no_common_edge _ _ hBD a b' hzB hDab
        | inr au =>
          rw [ordinaryWheelResources_spoke] at hz hzB
          have hhub:u (e j)=u i:=(hG j).1.symm.trans (hz.1.trans (hzB.1.symm.trans hBu))
          have he:=congrArg Fin.val (hu hhub)
          have hj':=j.isLt
          dsimp [e,i] at he
          omega
      have hload:∀ a,rootWheelInternalLoad (Fin.snoc C B) x (Fin.snoc vv (v i)) (Fin.snoc ww (w i)) a≤K:=by
        intro a
        rw [rootWheelInternalLoad_snoc]
        by_cases ha:a∈rootWheelInternal B x (v i) (w i)
        · rw [if_pos ha]
          have hsupport:a∈(ordinaryWheelRim B).support:=Set.mem_toFinset.mp (Finset.mem_sdiff.mp ha).1
          have hnot:a∉S:=by
            rcases hBA a hsupport with hroots|hA
            · exact ((Finset.mem_sdiff.mp ha).2 hroots).elim
            · exact hA.2
          have hh:rootWheelInternalLoad C x vv ww a<K:=by simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using hnot
          omega
        · rw [if_neg ha,Nat.add_zero];exact hcap' a
      have hvprefix:(fun j:Fin (k+1)=>v ⟨j.val,lt_of_lt_of_le j.isLt hk⟩)=Fin.snoc vv (v i):=by
        funext j
        refine Fin.lastCases ?_ (fun j=>?_) j
        · simp only [Fin.snoc_last];rfl
        · simp only [Fin.snoc_castSucc];rfl
      have hwprefix:(fun j:Fin (k+1)=>w ⟨j.val,lt_of_lt_of_le j.isLt hk⟩)=Fin.snoc ww (w i):=by
        funext j
        refine Fin.lastCases ?_ (fun j=>?_) j
        · simp only [Fin.snoc_last];rfl
        · simp only [Fin.snoc_castSucc];rfl
      refine ⟨Fin.snoc C B,?_,?_,?_⟩
      · intro j
        refine Fin.lastCases ?_ (fun j=>?_) j
        · simpa only [Fin.snoc_last,Fin.val_last,i] using hB
        · simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using hG j
      · intro j l
        refine Fin.lastCases ?_ (fun j'=>?_) j
        · refine Fin.lastCases ?_ (fun l'=>?_) l
          · intro hne;exact (hne rfl).elim
          · intro _;simpa only [Fin.snoc_last,Fin.snoc_castSucc] using (hcross l').symm
        · refine Fin.lastCases ?_ (fun l'=>?_) l
          · intro _;simpa only [Fin.snoc_last,Fin.snoc_castSucc] using hcross j'
          · intro hne
            simpa only [Fin.snoc_castSucc] using hdis j' l' (fun he=>hne (congrArg Fin.castSucc he))
      · rw [hvprefix,hwprefix]
        exact hload
  obtain ⟨C,hC,hdis,hcap⟩:=hprefix N le_rfl
  have he:(fun i:Fin N=>v ⟨i.val,lt_of_lt_of_le i.isLt le_rfl⟩)=v:=rfl
  have he':(fun i:Fin N=>w ⟨i.val,lt_of_lt_of_le i.isLt le_rfl⟩)=w:=rfl
  rw [he,he'] at hcap
  have hdegree:∀ a,a≠x → (wheelFamilyRim C).degree a≤2*(K+1):=
    fun a ha=>rootWheelFamily_degree C x v w K (disjoint_pairs_endpoint_count v w hpair) hcap a ha
  have hexact:=root_wheel_family_exact_edges C x v w u hvw (fun i=>(hC i).1)
    (fun i=>(hC i).2.1) (fun i=>(hC i).2.2.1)
  refine ⟨C,hC,hdis,hcap,hdegree,hexact.1,hexact.2,?_,?_⟩
  · intro a ha
    have hd:=hdegree a ha
    rw [wheelFamily_rim_degree_spoke_degree C hdis a] at hd
    omega
  · intro b'
    apply wheelFamily_injective_hub_degree C ?_ b'
    intro i j he
    apply hu
    exact (hC i).1.symm.trans (he.trans (hC j).1)

end Oberwolfach
