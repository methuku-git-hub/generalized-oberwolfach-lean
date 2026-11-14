module

public import Oberwolfach.OrdinaryJointFreshEmbeddings

@[expose] public section

/-! Simultaneous fresh expansion embeddings with all numerical allowances
discharged by the total finite model size. The family may have different old
row, old hub, edge and spoke identifier types at every index. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_joint_expansion_embeddings (l M r:ℕ) (hr:3≤r)
    (Vd Ud E J:Fin l→Type) [∀ i,Fintype (Vd i)] [∀ i,Fintype (Ud i)]
    [∀ i,Fintype (E i)] [∀ i,Fintype (J i)]
    [∀ i,DecidableEq (Vd i)] [∀ i,DecidableEq (Ud i)]
    [∀ i,DecidableEq (E i)] [∀ i,DecidableEq (J i)]
    (x y:∀ i,E i→Vd i) (v:∀ i,J i→Vd i) (u:∀ i,J i→Ud i)
    (hsize:∀ i,Fintype.card (Vd i)+Fintype.card (Ud i)+
      (Fintype.card (E i)+Fintype.card (J i))*(r+1)≤M)
    (Q F:SimpleGraph V) (H:V→U→Prop) (A W R:Finset V) (B:Finset U)
    (d c cH:ℝ) (hd:0≤d) (hF:∀ v,(F.degree v:ℝ)≤d)
    (hA:c≤(A.card:ℝ)) (hU:cH≤(Fintype.card U:ℝ))
    (hcount:∀ v w,c≤((A∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hpair:∀ a b v w,c≤(((A.filter (fun z=>H z a∧H z b))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hhub:∀ T:Finset V,T.card≤r→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
      cH≤((common Finset.univ T (fun v=>Finset.univ.filter (H v))).card:ℝ))
    (hbudget:W.card+((R.card:ℝ)+(l+1)*M+r+6)*(d+1)<c)
    (hB:(B.card:ℝ)+(l+1)*M<cH) :
    ∃ e:∀ i:Fin l,OrdinaryPairHostEmbedding
      (ordinaryExpansionRim (J:=J i) (SimpleGraph.cycleGraph r) ⟨0,by omega⟩ ⟨r-1,by omega⟩ (x i) (y i))
      (ordinaryExpansionSpokes (E:=E i) ⟨0,by omega⟩ (v i) (u i)) Q H,
      (∀ i,(e i).IsFresh F A W R B)∧
      (∀ i j,i≠j→∀ a:ExpansionRow (Vd i) (E i) (J i) (Fin r),
        ∀ b:ExpansionRow (Vd j) (E j) (J j) (Fin r),(e i).row a≠(e j).row b)∧
      (∀ i j,i≠j→∀ a:ExpansionHub (Ud i) (E i) (J i),
        ∀ b:ExpansionHub (Ud j) (E j) (J j),(e i).hub a≠(e j).hub b)∧
      (∀ i j,i≠j→∀ a:ExpansionRow (Vd i) (E i) (J i) (Fin r),
        ∀ b:ExpansionRow (Vd j) (E j) (J j) (Fin r),¬F.Adj ((e i).row a) ((e j).row b)) := by
  have hrow:∀ i,Fintype.card (Vd i)+(Fintype.card (E i)+Fintype.card (J i))*r≤M:=by
    intro i
    have hi:=hsize i
    rw [Nat.mul_add,Nat.mul_one] at hi
    omega
  have hhubc:∀ i,Fintype.card (Ud i)+Fintype.card (E i)+Fintype.card (J i)≤M:=by
    intro i
    have hi:=hsize i
    rw [Nat.mul_add,Nat.mul_one] at hi
    omega
  apply ordinary_joint_fresh_embeddings l M
    (fun i=>ExpansionRow (Vd i) (E i) (J i) (Fin r))
    (fun i=>ExpansionHub (Ud i) (E i) (J i)) _ _ Q F H A W R B
  · intro i
    simpa [ExpansionRow,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using hrow i
  · intro i
    simpa [ExpansionHub,Fintype.card_sum,Nat.add_assoc] using hhubc i
  · intro R' B' hRR hBB hRc hBc i
    apply ordinary_fresh_expansion_pair_embedding Q F H A W R' B' (x i) (y i) (v i) (u i)
      r hr d c cH hd hF hA hU hcount hpair hhub
    · have hrc:(R'.card:ℝ)≤R.card+l*M:=by exact_mod_cast hRc
      have hmod:(Fintype.card (Vd i):ℝ)+Fintype.card (E i⊕J i)*r≤M:=by
        simpa only [Fintype.card_sum,Nat.cast_add,Nat.cast_mul] using
          (show ((Fintype.card (Vd i)+(Fintype.card (E i)+Fintype.card (J i))*r:ℕ):ℝ)≤M from by exact_mod_cast hrow i)
      have hm:=mul_le_mul_of_nonneg_right (show (R'.card:ℝ)+Fintype.card (Vd i)+Fintype.card (E i⊕J i)*r+r+6≤R.card+(l+1)*M+r+6 by linarith only [hrc,hmod])
        (by linarith:(0:ℝ)≤d+1)
      linarith only [hbudget,hm]
    · have hbc:(B'.card:ℝ)≤B.card+l*M:=by exact_mod_cast hBc
      have hmod:(Fintype.card (Ud i):ℝ)+Fintype.card (E i⊕J i)≤M:=by
        simpa only [Fintype.card_sum,Nat.cast_add,add_assoc] using
          (show ((Fintype.card (Ud i)+Fintype.card (E i)+Fintype.card (J i):ℕ):ℝ)≤M from by exact_mod_cast hhubc i)
      linarith only [hB,hbc,hmod]

end Oberwolfach
