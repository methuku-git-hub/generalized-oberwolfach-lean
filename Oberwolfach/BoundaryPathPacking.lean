module

public import Oberwolfach.BoundaryWheelExtension
public import Oberwolfach.BoundaryWheelLoads
public import Oberwolfach.GreedyGraphCandidates

@[expose] public section

/-! Simultaneous completion of prescribed boundary pairs to actual wheels.
The reserved spokes remain available for their own pairs. A cap is imposed
only on free vertices, and all losses are charged at their realised size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem boundary_path_wheel_packing (Q D₀ F:SimpleGraph V) (H E₀ R:V→U→Prop)
    (X:Finset V) (N r K D:ℕ) (hr:4≤r) (hK:0<K)
    (x v w:Fin N→V) (u:Fin N→U) (hx:∀ i,x i∉X) (hv:∀ i,v i∈X) (hw:∀ i,w i∈X)
    (hvw:∀ i,v i≠w i) (hxv:∀ i,Q.Adj (x i) (v i)) (hxw:∀ i,Q.Adj (x i) (w i))
    (hDxv:∀ i,¬D₀.Adj (x i) (v i)) (hDxw:∀ i,¬D₀.Adj (x i) (w i))
    (hpair:∀ i j,i≠j→x i=x j→Disjoint ({v i,w i}:Finset V) {v j,w j})
    (hspoke:∀ i j,i≠j→u i=u j→Disjoint ({x i,v i,w i}:Finset V) {x j,v j,w j})
    (hroot:∀ i,∀ a∈({x i,v i,w i}:Finset V),H a (u i) ∧ ¬E₀ a (u i) ∧ R a (u i))
    (hFroot:∀ i,∀ a∈({x i,v i,w i}:Finset V),∀ c∈({x i,v i,w i}:Finset V),¬F.Adj a c)
    (hend:∀ a,(Finset.univ.filter (fun i=>a∈({x i,v i,w i}:Finset V))).card≤D)
    (hhub:∀ z,(Finset.univ.filter (fun i=>u i=z)).card≤D)
    (L d₀ e₀ s b:ℝ) (hL:0≤L) (hF:∀ a,(F.degree a:ℝ)≤L)
    (hD₀:∀ a∈X,(D₀.degree a:ℝ)≤d₀)
    (hE₀:∀ z,((Finset.univ.filter (fun a=>E₀ a z)).card:ℝ)≤e₀)
    (hR:∀ z,((Finset.univ.filter (fun a=>R a z)).card:ℝ)≤s)
    (hcount:∀ i,∀ a∈X,∀ c∈X,b≤(((X.filter (fun z=>H z (u i)))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ))
    (hbudget:(N*r:ℕ)/(K:ℝ)+((r:ℝ)+3)*(L+1)+2*(d₀+2*(K+D:ℕ))+e₀+(D*r:ℕ)+s<b):
    ∃ C:Fin N→OrdinaryWheel Q F H r,
      (∀ i,ordinaryWheelHub (C i)=u i ∧ (ordinaryWheelRim (C i)).Adj (x i) (v i) ∧
        (ordinaryWheelRim (C i)).Adj (x i) (w i) ∧
        (∀ a∈(ordinaryWheelRim (C i)).support,a=x i∨a∈X) ∧
        Disjoint (ordinaryWheelResources (C i)) (ordinaryHostResources D₀ E₀) ∧
        (∀ a∈(ordinaryWheelRim (C i)).support,R a (u i)→a∈({x i,v i,w i}:Finset V))) ∧
      (∀ i j,i≠j→Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j))) ∧
      (∀ a,boundaryWheelFreeLoad C x v w a≤K) ∧
      (∀ a,(wheelFamilyRim C).degree a≤2*(K+D)) ∧
      (∀ a,(Finset.univ.filter (fun z=>wheelFamilySpokes C a z)).card≤K+D) ∧
      (∀ z,(Finset.univ.filter (fun a=>wheelFamilySpokes C a z)).card≤D*r):=by
  let Good (i:Fin N) (C:OrdinaryWheel Q F H r):=
    ordinaryWheelHub C=u i ∧ (ordinaryWheelRim C).Adj (x i) (v i) ∧
      (ordinaryWheelRim C).Adj (x i) (w i) ∧
      (∀ a∈(ordinaryWheelRim C).support,a=x i∨a∈X) ∧
      Disjoint (ordinaryWheelResources C) (ordinaryHostResources D₀ E₀) ∧
      (∀ a∈(ordinaryWheelRim C).support,R a (u i)→a∈({x i,v i,w i}:Finset V))
  have hprefix:∀ k:ℕ,∀ hk:k≤N,∃ C:Fin k→OrdinaryWheel Q F H r,
      (∀ j,Good ⟨j.val,lt_of_lt_of_le j.isLt hk⟩ (C j)) ∧
      (∀ i j,i≠j→Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j))) ∧
      (∀ a,boundaryWheelFreeLoad C
        (fun j=>x ⟨j.val,lt_of_lt_of_le j.isLt hk⟩)
        (fun j=>v ⟨j.val,lt_of_lt_of_le j.isLt hk⟩)
        (fun j=>w ⟨j.val,lt_of_lt_of_le j.isLt hk⟩) a≤K):=by
    intro k
    induction k with
    | zero=>
      intro hk
      refine ⟨Fin.elim0,fun i=>Fin.elim0 i,fun i=>Fin.elim0 i,?_⟩
      intro a;simp [boundaryWheelFreeLoad]
    | succ k ih=>
      intro hk
      have hkN:k≤N:=by omega
      obtain ⟨C,hC,hdis,hcap⟩:=ih hkN
      let e:Fin k↪Fin N:=⟨fun j=>⟨j.val,lt_of_lt_of_le j.isLt hkN⟩,
        by intro a b he;exact Fin.ext (congrArg (fun z:Fin N=>z.val) he)⟩
      let i:Fin N:=⟨k,by omega⟩
      have hei (j:Fin k):e j≠i:=by
        intro he;have hh:=congrArg Fin.val he;have hj:=j.isLt;dsimp [e,i] at hh;omega
      let xx:Fin k→V:=fun j=>x (e j)
      let vv:Fin k→V:=fun j=>v (e j)
      let ww:Fin k→V:=fun j=>w (e j)
      have hcap':∀ a,boundaryWheelFreeLoad C xx vv ww a≤K:=hcap
      have hend' (a:V):(Finset.univ.filter (fun j=>a∈({xx j,vv j,ww j}:Finset V))).card≤D:=by
        apply le_trans _ (hend a)
        apply Finset.card_le_card_of_injOn e
        · intro j hj;exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2⟩
        · intro j _ l _ h;exact e.injective h
      have hload:∀ a,wheelRimLoad C a≤K+D:=boundaryWheel_load_bound C xx vv ww K D hcap' hend'
      have hhub' (z:U):wheelHubLoad C z≤D:=by
        apply le_trans _ (hhub z)
        apply Finset.card_le_card_of_injOn e
        · intro j hj
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hC j).1.symm.trans (Finset.mem_filter.mp hj).2⟩
        · intro j _ l _ h;exact e.injective h
      let DR:=D₀⊔wheelFamilyRim C
      let ER:V→U→Prop:=fun a z=>E₀ a z ∨ wheelFamilySpokes C a z ∨
        (R a z ∧ ¬(z=u i∧a∈({x i,v i,w i}:Finset V)))
      let W:=Finset.univ.filter (fun a=>K≤boundaryWheelFreeLoad C xx vv ww a)
      have hW:(W.card:ℝ)≤(N*r:ℕ)/(K:ℝ):=by
        apply (le_div_iff₀ (Nat.cast_pos.mpr hK)).mpr
        have hh:K*W.card≤N*r:=(boundaryWheelFreeLoad_saturated C xx vv ww K).trans
          (by simp only [Fintype.card_fin];exact Nat.mul_le_mul_right r hkN)
        exact_mod_cast (by simpa only [Nat.mul_comm] using hh)
      have hDR (a:V) (ha:a∈X):(DR.degree a:ℝ)≤d₀+2*(K+D:ℕ):=by
        have hh:(DR.degree a:ℝ)≤D₀.degree a+(wheelFamilyRim C).degree a:=by
          exact_mod_cast graph_degree_sup_le D₀ (wheelFamilyRim C) a
        have hl:( (wheelFamilyRim C).degree a:ℝ)≤2*(K+D:ℕ):=by
          exact_mod_cast (wheelRimLoad_degree C a).trans (Nat.mul_le_mul_left 2 (hload a))
        linarith only [hh,hl,hD₀ a ha]
      have hER (z:U):((Finset.univ.filter (fun a=>ER a z)).card:ℝ)≤e₀+(D*r:ℕ)+s:=by
        have hs:Finset.univ.filter (fun a=>ER a z)⊆
            (Finset.univ.filter (fun a=>E₀ a z))∪
              ((Finset.univ.filter (fun a=>wheelFamilySpokes C a z))∪(Finset.univ.filter (fun a=>R a z))):=by
          intro a ha
          simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,ER] at ha ⊢
          tauto
        have hh:=(Finset.card_le_card hs).trans ((Finset.card_union_le _ _).trans
          (Nat.add_le_add_left (Finset.card_union_le _ _) _))
        have hh':((Finset.univ.filter (fun a=>ER a z)).card:ℝ)≤
            (Finset.univ.filter (fun a=>E₀ a z)).card+
            ((Finset.univ.filter (fun a=>wheelFamilySpokes C a z)).card+
              (Finset.univ.filter (fun a=>R a z)).card):=by exact_mod_cast hh
        have hu:((Finset.univ.filter (fun a=>wheelFamilySpokes C a z)).card:ℝ)≤(D*r:ℕ):=by
          exact_mod_cast (wheelHubLoad_spoke_column C z).trans (Nat.mul_le_mul_right r (hhub' z))
        linarith only [hh',hu,hE₀ z,hR z]
      have hnewrim (a:V) (ha:a∈({v i,w i}:Finset V)):¬(wheelFamilyRim C).Adj (x i) a:=by
        intro hxa
        obtain ⟨j,hj⟩:=SimpleGraph.iSup_adj.mp hxa
        have hxi:x i=x (e j):=by
          rcases (hC j).2.2.2.1 _ hj.mem_support_left with he|he
          · exact he
          · exact (hx i he).elim
        have hneigh:=ordinaryWheel_root_neighbors (C j) (x (e j)) (v (e j)) (w (e j))
          (hvw (e j)) (hC j).2.1 (hC j).2.2.1
        have haj:a∈({v (e j),w (e j)}:Finset V):=by
          rw [←hneigh]
          exact ((ordinaryWheelRim (C j)).mem_neighborFinset _ _).mpr (hxi ▸ hj)
        exact Finset.disjoint_left.mp (hpair (e j) i (hei j) hxi.symm) haj ha
      have hnewspoke (a:V) (ha:a∈({x i,v i,w i}:Finset V)):¬ER a (u i):=by
        intro hbad
        rcases hbad with hbad|hbad|hbad
        · exact (hroot i a ha).2.1 hbad
        · obtain ⟨j,hju,hja⟩:=hbad
          have he:u (e j)=u i:=(hC j).1.symm.trans hju
          have hRa:R a (u (e j)):=he.symm ▸ (hroot i a ha).2.2
          have haj:=(hC j).2.2.2.2.2 a hja hRa
          exact Finset.disjoint_left.mp (hspoke (e j) i (hei j) he) haj ha
        · exact hbad.2 ⟨rfl,ha⟩
      obtain ⟨C',hCu,hCv,hCw,havoid,hfree⟩:=boundary_wheel_after_deletion Q DR F H ER
        (X.filter (fun a=>H a (u i))) W X (Finset.filter_subset _ _) (x i) (v i) (w i) (u i)
        (hv i) (hw i) (hvw i) (hxv i) (hxw i)
        (fun hh=>hh.elim (hDxv i) (hnewrim _ (by simp)))
        (fun hh=>hh.elim (hDxw i) (hnewrim _ (by simp))) (hFroot i)
        ⟨(hroot i _ (by simp)).1,(hroot i _ (by simp)).1,(hroot i _ (by simp)).1⟩
        ⟨hnewspoke _ (by simp),hnewspoke _ (by simp),hnewspoke _ (by simp)⟩
        (fun a ha=>(Finset.mem_filter.mp ha).2) r hr L (d₀+2*(K+D:ℕ)) (e₀+(D*r:ℕ)+s) b hL hF
        (by intro a ha;simpa only [←SimpleGraph.ncard_neighborSet] using hDR a ha)
        (by convert hER (u i) using 1;congr 2;ext a;simp only [Finset.mem_filter])
        (hcount i) (by linarith only [hbudget,hW])
      have hfixed:Disjoint (ordinaryWheelResources C') (ordinaryHostResources D₀ E₀):=by
        apply havoid.mono_right
        intro z hz
        cases z with
        | inl edge=>
          rw [ordinaryHostResources_rim] at hz ⊢
          induction edge using Sym2.ind with
          | _ a c=>exact Or.inl hz
        | inr az=>
          rw [ordinaryHostResources_spoke] at hz ⊢
          exact Or.inl hz
      have hreserved:∀ a∈(ordinaryWheelRim C').support,R a (u i)→a∈({x i,v i,w i}:Finset V):=by
        intro a ha hRai
        by_contra hn
        exact Finset.disjoint_left.mp havoid
          ((ordinaryWheelResources_spoke C' a (u i)).mpr ⟨hCu,ha⟩)
          ((ordinaryHostResources_spoke DR ER a (u i)).mpr (Or.inr (Or.inr ⟨hRai,by tauto⟩)))
      have hGood:Good i C':=by
        refine ⟨hCu,hCv,hCw,?_,hfixed,hreserved⟩
        intro a ha
        rcases hfree a ha with hroot|hfree
        · simp only [Finset.mem_insert,Finset.mem_singleton] at hroot
          rcases hroot with rfl|rfl|rfl
          · exact Or.inl rfl
          · exact Or.inr (hv i)
          · exact Or.inr (hw i)
        · exact Or.inr (Finset.mem_filter.mp hfree.1).1
      have hcross (j:Fin k):Disjoint (ordinaryWheelResources (C j)) (ordinaryWheelResources C'):=by
        apply (havoid.mono_right ?_).symm
        intro z hz
        cases z with
        | inl edge=>
          rw [ordinaryWheelResources_rim] at hz
          rw [ordinaryHostResources_rim]
          induction edge using Sym2.ind with
          | _ a c=>exact Or.inr (SimpleGraph.iSup_adj.mpr ⟨j,hz⟩)
        | inr az=>
          rcases az with ⟨a,z⟩
          rw [ordinaryWheelResources_spoke] at hz
          rw [ordinaryHostResources_spoke]
          exact Or.inr (Or.inl ⟨j,hz⟩)
      have hload':∀ a,boundaryWheelFreeLoad (Fin.snoc C C') (Fin.snoc xx (x i))
          (Fin.snoc vv (v i)) (Fin.snoc ww (w i)) a≤K:=by
        intro a
        rw [boundaryWheelFreeLoad_snoc]
        by_cases ha:a∈rootWheelInternal C' (x i) (v i) (w i)
        · rw [if_pos ha]
          have hs:a∈(ordinaryWheelRim C').support:=Set.mem_toFinset.mp (Finset.mem_sdiff.mp ha).1
          have hn:a∉W:=by
            rcases hfree a hs with hroot|hfree
            · exact ((Finset.mem_sdiff.mp ha).2 hroot).elim
            · exact hfree.2
          have hh:boundaryWheelFreeLoad C xx vv ww a<K:=by
            simpa only [W,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using hn
          omega
        · rw [if_neg ha,Nat.add_zero];exact hcap' a
      have heq (f:Fin N→V):
          (fun j:Fin (k+1)=>f ⟨j.val,lt_of_lt_of_le j.isLt hk⟩)=Fin.snoc (fun j=>f (e j)) (f i):=by
        funext j
        refine Fin.lastCases ?_ (fun j=>?_) j
        · simp only [Fin.snoc_last];rfl
        · simp only [Fin.snoc_castSucc];rfl
      refine ⟨Fin.snoc C C',?_,?_,?_⟩
      · intro j
        refine Fin.lastCases ?_ (fun j=>?_) j
        · simpa only [Fin.snoc_last,Fin.val_last,i] using hGood
        · simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using hC j
      · intro j l
        refine Fin.lastCases ?_ (fun j'=>?_) j
        · refine Fin.lastCases ?_ (fun l'=>?_) l
          · intro hne;exact (hne rfl).elim
          · intro _;simpa only [Fin.snoc_last,Fin.snoc_castSucc] using (hcross l').symm
        · refine Fin.lastCases ?_ (fun l'=>?_) l
          · intro _;simpa only [Fin.snoc_last,Fin.snoc_castSucc] using hcross j'
          · intro hne;simpa only [Fin.snoc_castSucc] using hdis j' l' (fun he=>hne (congrArg Fin.castSucc he))
      · rw [heq x,heq v,heq w]
        exact hload'
  obtain ⟨C,hC,hdis,hcap⟩:=hprefix N le_rfl
  have hcap':∀ a,boundaryWheelFreeLoad C x v w a≤K:=hcap
  have hload:=boundaryWheel_load_bound C x v w K D hcap' hend
  refine ⟨C,hC,hdis,hcap',?_,?_,?_⟩
  · intro a;exact (wheelRimLoad_degree C a).trans (Nat.mul_le_mul_left 2 (hload a))
  · intro a;exact (wheelRimLoad_spoke_row C a).trans (hload a)
  · intro z
    have hh:wheelHubLoad C z≤D:=by
      have he:Finset.univ.filter (fun i=>ordinaryWheelHub (C i)=z)=Finset.univ.filter (fun i=>u i=z):=by
        ext i;simp only [Finset.mem_filter,Finset.mem_univ,true_and,(hC i).1]
      dsimp [wheelHubLoad];rw [he];exact hhub z
    exact (wheelHubLoad_spoke_column C z).trans (Nat.mul_le_mul_right r hh)

end Oberwolfach
