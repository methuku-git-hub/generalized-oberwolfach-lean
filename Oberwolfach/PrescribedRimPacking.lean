module

public import Oberwolfach.WheelLoadBounds
public import Oberwolfach.PrescribedRimDeletion

@[expose] public section

/-! A degree-controlled ordinary wheel packing through a prescribed family
of rim edges. All other rim vertices lie in X and every hub lies in B.
The hypotheses are explicit common-neighbour counts, not an extension oracle. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem prescribed_rim_wheel_packing (Q F:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (B:Finset U) (N r K D₀:ℕ) (hr:3≤r) (hK:0<K)
    (x y:Fin N→V) (hx:∀ i,x i∉X) (hy:∀ i,y i∉X)
    (hxy:∀ i,Q.Adj (x i) (y i)) (hFxy:∀ i,¬F.Adj (x i) (y i))
    (hedge:∀ i j,i≠j → ¬((x i=x j∧y i=y j)∨(x i=y j∧y i=x j)))
    (hend:∀ a,(Finset.univ.filter (fun i=>a=x i∨a=y i)).card≤D₀)
    (L bV bU:ℝ) (hL:0≤L) (hF:∀ a,(F.degree a:ℝ)≤L)
    (hcount:∀ u∈B,∀ a c,bV≤(((X.filter (fun v=>H v u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ))
    (hubs:∀ i,bU≤((B.filter (fun u=>H (x i) u∧H (y i) u)).card:ℝ))
    (hbudgetV:(N*r:ℕ)/(K:ℝ)+(K*r:ℕ)+((r:ℝ)+2)*(L+1)+4*(K+D₀:ℕ)<bV)
    (hbudgetU:(N:ℝ)/K+2*(K+D₀:ℕ)<bU) :
    ∃ C:Fin N→OrdinaryWheel Q F H r,
      (∀ i,ordinaryWheelHub (C i)∈B ∧ (ordinaryWheelRim (C i)).Adj (x i) (y i) ∧
        ∀ a∈(ordinaryWheelRim (C i)).support,a=x i∨a=y i∨a∈X) ∧
      (∀ i j,i≠j → Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j))) ∧
      (∀ a∈X,wheelRimLoad C a≤K) ∧ (∀ u,wheelHubLoad C u≤K) ∧
      (∀ a,(wheelFamilyRim C).degree a≤2*(K+D₀)) ∧
      (∀ a,(Finset.univ.filter (fun u=>wheelFamilySpokes C a u)).card≤K+D₀) ∧
      (∀ u,(Finset.univ.filter (fun a=>wheelFamilySpokes C a u)).card≤K*r) :=by
  let Good (i:Fin N) (C:OrdinaryWheel Q F H r):=
    ordinaryWheelHub C∈B ∧ (ordinaryWheelRim C).Adj (x i) (y i) ∧
      ∀ a∈(ordinaryWheelRim C).support,a=x i∨a=y i∨a∈X
  have load_bound {k:ℕ} (e:Fin k↪Fin N) (C:Fin k→OrdinaryWheel Q F H r)
      (hC:∀ j,Good (e j) (C j)) (hcap:∀ a∈X,wheelRimLoad C a≤K) (a:V):wheelRimLoad C a≤K+D₀:=by
    by_cases ha:a∈X
    · exact (hcap a ha).trans (Nat.le_add_right _ _)
    · have hh:wheelRimLoad C a≤(Finset.univ.filter (fun i=>a=x i∨a=y i)).card:=by
        apply Finset.card_le_card_of_injOn e
        · intro j hj
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
          rcases (hC j).2.2 a (Finset.mem_filter.mp hj).2 with h|h|h
          · exact Or.inl h
          · exact Or.inr h
          · exact (ha h).elim
        · intro i _ j _ hij;exact e.injective hij
      exact (hh.trans (hend a)).trans (Nat.le_add_left _ _)
  have hp:∀ k:ℕ,∀ hk:k≤N,∃ C:Fin k→OrdinaryWheel Q F H r,
      (∀ j,Good ⟨j.val,lt_of_lt_of_le j.isLt hk⟩ (C j)) ∧
      (∀ i j,i≠j → Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j))) ∧
      (∀ a∈X,wheelRimLoad C a≤K) ∧ ∀ u,wheelHubLoad C u≤K:=by
    intro k
    induction k with
    | zero =>
      intro hk
      refine ⟨Fin.elim0,fun j=>Fin.elim0 j,fun i=>Fin.elim0 i,?_,?_⟩
      · intro a _;simp [wheelRimLoad]
      · intro u;simp [wheelHubLoad]
    | succ k ih =>
      intro hk
      have hkN:k≤N:=by omega
      obtain ⟨C,hC,hdis,hcap,hucap⟩:=ih hkN
      let e:Fin k↪Fin N:=⟨fun j=>⟨j.val,lt_of_lt_of_le j.isLt hkN⟩,by intro a b h;exact Fin.ext (congrArg (fun z:Fin N=>z.val) h)⟩
      let i:Fin N:=⟨k,by omega⟩
      have hl (a:V):wheelRimLoad C a≤K+D₀:=load_bound e C hC hcap a
      let D:=wheelFamilyRim C
      let S:=Finset.univ.filter (fun a=>K≤wheelRimLoad C a)
      let T:=Finset.univ.filter (fun u=>K≤wheelHubLoad C u)
      have hS:(S.card:ℝ)≤(N*r:ℕ)/(K:ℝ):=by
        apply (le_div_iff₀ (Nat.cast_pos.mpr hK)).mpr
        have hh:K*S.card≤N*r:=(wheelRimLoad_saturated C K).trans (by simp only [Fintype.card_fin];exact Nat.mul_le_mul_right r hkN)
        exact_mod_cast (by simpa only [Nat.mul_comm] using hh)
      have hT:(T.card:ℝ)≤(N:ℝ)/K:=by
        apply (le_div_iff₀ (Nat.cast_pos.mpr hK)).mpr
        have hh:K*T.card≤N:=(wheelHubLoad_saturated C K).trans (by simpa only [Fintype.card_fin] using hkN)
        exact_mod_cast (by simpa only [Nat.mul_comm] using hh)
      let Rx:=Finset.univ.filter (fun u=>wheelFamilySpokes C (x i) u)
      let Ry:=Finset.univ.filter (fun u=>wheelFamilySpokes C (y i) u)
      have hRx:Rx.card≤K+D₀:=(wheelRimLoad_spoke_row C (x i)).trans (hl (x i))
      have hRy:Ry.card≤K+D₀:=(wheelRimLoad_spoke_row C (y i)).trans (hl (y i))
      have hbad:((T∪(Rx∪Ry)).card:ℝ)≤(N:ℝ)/K+2*(K+D₀:ℕ):=by
        have hc:(T∪(Rx∪Ry)).card≤T.card+2*(K+D₀):=by
          have hh:=(Finset.card_union_le T (Rx∪Ry)).trans (Nat.add_le_add_left (Finset.card_union_le Rx Ry) T.card)
          omega
        have hc':((T∪(Rx∪Ry)).card:ℝ)≤T.card+2*(K+D₀:ℕ):=by exact_mod_cast hc
        linarith only [hc',hT]
      have hc:(T∪(Rx∪Ry)).card<(B.filter (fun u=>H (x i) u∧H (y i) u)).card:=by
        have hh:=lt_of_le_of_lt hbad (lt_of_lt_of_le hbudgetU (hubs i))
        exact_mod_cast hh
      obtain ⟨u,hu,havoid⟩:=Finset.exists_mem_notMem_of_card_lt_card hc
      have huB:u∈B:=(Finset.mem_filter.mp hu).1
      have hux:H (x i) u:=(Finset.mem_filter.mp hu).2.1
      have huy:H (y i) u:=(Finset.mem_filter.mp hu).2.2
      have huT:u∉T:=fun h=>havoid (Finset.mem_union_left _ h)
      have huxold:¬wheelFamilySpokes C (x i) u:=fun h=>havoid (Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)))
      have huyold:¬wheelFamilySpokes C (y i) u:=fun h=>havoid (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)))
      let Z:=Finset.univ.filter (fun a=>wheelFamilySpokes C a u)
      have hZ:Z.card≤K*r:=(wheelHubLoad_spoke_column C u).trans (Nat.mul_le_mul_right r (hucap u))
      have hW:((S∪Z).card:ℝ)≤(N*r:ℕ)/(K:ℝ)+(K*r:ℕ):=by
        have hh:((S∪Z).card:ℝ)≤S.card+Z.card:=by exact_mod_cast Finset.card_union_le S Z
        have hz:(Z.card:ℝ)≤(K*r:ℕ):=by exact_mod_cast hZ
        linarith only [hh,hS,hz]
      have hD:∀ a,(D.degree a:ℝ)≤2*(K+D₀:ℕ):=by
        intro a
        exact_mod_cast (wheelRimLoad_degree C a).trans (Nat.mul_le_mul_left 2 (hl a))
      have hnew:¬D.Adj (x i) (y i):=by
        intro h
        obtain ⟨j,hj⟩:=SimpleGraph.iSup_adj.mp h
        have hne:i≠e j:=by intro he;have he':=congrArg Fin.val he;have hj':=j.isLt;dsimp [e,i] at he';omega
        have hxj:x i=x (e j)∨x i=y (e j):=by
          rcases (hC j).2.2 (x i) hj.mem_support_left with h|h|h
          · exact Or.inl h
          · exact Or.inr h
          · exact (hx i h).elim
        have hyj:y i=x (e j)∨y i=y (e j):=by
          rcases (hC j).2.2 (y i) hj.mem_support_right with h|h|h
          · exact Or.inl h
          · exact Or.inr h
          · exact (hy i h).elim
        rcases hxj with hxj|hxj <;> rcases hyj with hyj|hyj
        · exact (hxy i).ne (hxj.trans hyj.symm)
        · exact hedge i (e j) hne (Or.inl ⟨hxj,hyj⟩)
        · exact hedge i (e j) hne (Or.inr ⟨hxj,hyj⟩)
        · exact (hxy i).ne (hxj.trans hyj.symm)
      obtain ⟨W,hWu,hWxy,hWD,hWs⟩:=ordinary_rim_edge_wheel_after_deletion Q D F H
        (X.filter (fun a=>H a u)) (S∪Z) (x i) (y i) u (hxy i) hnew (hFxy i) hux huy
        (by intro a ha;exact (Finset.mem_filter.mp ha).2) r hr L (2*(K+D₀:ℕ)) bV hL hF hD
        (hcount u huB) (by linarith only [hW,hbudgetV])
      have hWG:Good i W:=⟨by rw [hWu];exact huB,hWxy,by
        intro a ha
        rcases hWs a ha with h|h|h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Finset.mem_filter.mp h.1).1)⟩
      have hcross (j:Fin k):Disjoint (ordinaryWheelResources (C j)) (ordinaryWheelResources W):=by
        apply Finset.disjoint_left.mpr
        intro z hz hzW
        cases z with
        | inl z =>
          rw [ordinaryWheelResources_rim] at hz hzW
          induction z using Sym2.inductionOn with
          | _ a b =>
            exact disjoint_graphs_no_common_edge _ _ hWD a b hzW (SimpleGraph.iSup_adj.mpr ⟨j,hz⟩)
        | inr au =>
          rw [ordinaryWheelResources_spoke] at hz hzW
          have he:au.2=u:=hzW.1.symm.trans hWu
          have hold:wheelFamilySpokes C au.1 u:=⟨j,hz.1.trans he,hz.2⟩
          rcases hWs au.1 hzW.2 with h|h|h
          · rw [h] at hold;exact huxold hold
          · rw [h] at hold;exact huyold hold
          · exact h.2 (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hold⟩))
      refine ⟨Fin.snoc C W,?_,?_,?_,?_⟩
      · intro j
        refine Fin.lastCases ?_ (fun j=>?_) j
        · simpa only [Fin.snoc_last,Fin.val_last,i] using hWG
        · simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using hC j
      · intro j l
        refine Fin.lastCases ?_ (fun j'=>?_) j
        · refine Fin.lastCases ?_ (fun l'=>?_) l
          · intro h;exact (h rfl).elim
          · intro _;simpa only [Fin.snoc_last,Fin.snoc_castSucc] using (hcross l').symm
        · refine Fin.lastCases ?_ (fun l'=>?_) l
          · intro _;simpa only [Fin.snoc_last,Fin.snoc_castSucc] using hcross j'
          · intro h
            simpa only [Fin.snoc_castSucc] using hdis j' l' (fun he=>h (congrArg Fin.castSucc he))
      · intro a ha
        rw [wheelRimLoad_snoc]
        by_cases haw:a∈(ordinaryWheelRim W).support
        · rw [if_pos haw]
          have haS:a∉S:=by
            rcases hWs a haw with h|h|h
            · exact (hx i (h ▸ ha)).elim
            · exact (hy i (h ▸ ha)).elim
            · exact fun hs=>h.2 (Finset.mem_union_left _ hs)
          have hh:wheelRimLoad C a<K:=by simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using haS
          omega
        · rw [if_neg haw,Nat.add_zero];exact hcap a ha
      · intro v
        rw [wheelHubLoad_snoc]
        by_cases h:ordinaryWheelHub W=v
        · rw [if_pos h]
          have hv:v=u:=h.symm.trans hWu
          rw [hv]
          have hh:wheelHubLoad C u<K:=by simpa only [T,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using huT
          omega
        · rw [if_neg h,Nat.add_zero];exact hucap v
  obtain ⟨C,hC,hdis,hcap,hucap⟩:=hp N le_rfl
  have hl:∀ a,wheelRimLoad C a≤K+D₀:=load_bound (Function.Embedding.refl _) C hC hcap
  refine ⟨C,hC,hdis,hcap,hucap,?_,?_,?_⟩
  · intro a;exact (wheelRimLoad_degree C a).trans (Nat.mul_le_mul_left 2 (hl a))
  · intro a;exact (wheelRimLoad_spoke_row C a).trans (hl a)
  · intro u;exact (wheelHubLoad_spoke_column C u).trans (Nat.mul_le_mul_right r (hucap u))

end Oberwolfach
