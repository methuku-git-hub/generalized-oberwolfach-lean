module

public import Oberwolfach.PrescribedRimPacking
public import Oberwolfach.PrescribedSpokePacking
public import Oberwolfach.PrescribedEdgeProtection

@[expose] public section

/-! The two prescribed-edge constructions are assembled in the physical
rim/spoke representation. Every wheel meets the protected inner host in
exactly its designated edge, and the complete packing has bounded degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem prescribed_inner_edge_wheel_packing_supported (Q F:SimpleGraph V) (H:V→U→Prop)
    (I X:Finset V) (J B:Finset U) (hIX:Disjoint I X) (hJB:Disjoint J B)
    (Nr Ns r K D₀:ℕ) (hr:3≤r) (hK:0<K)
    (x y:Fin Nr→V) (hx:∀ i,x i∈I) (hy:∀ i,y i∈I)
    (hxy:∀ i,Q.Adj (x i) (y i)) (hFxy:∀ i,¬F.Adj (x i) (y i))
    (hedge:∀ i j,i≠j → ¬((x i=x j∧y i=y j)∨(x i=y j∧y i=x j)))
    (hend:∀ a,(Finset.univ.filter (fun i=>a=x i∨a=y i)).card≤D₀)
    (z:Fin Ns→V) (u:Fin Ns→U) (hz:∀ i,z i∈I) (hu:∀ i,u i∈J) (hH:∀ i,H (z i) (u i))
    (hspoke:Function.Injective (fun i=>(z i,u i)))
    (hsend:∀ a,(Finset.univ.filter (fun i=>a=z i)).card≤D₀)
    (hshub:∀ v,(Finset.univ.filter (fun i=>u i=v)).card≤D₀)
    (L bV bU:ℝ) (hL:0≤L) (hF:∀ a,(F.degree a:ℝ)≤L)
    (hcount:∀ v∈J∪B,∀ a c,bV≤(((X.filter (fun w=>H w v))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ))
    (hubs:∀ i,bU≤((B.filter (fun v=>H (x i) v∧H (y i) v)).card:ℝ))
    (hbudgetR:(Nr*r:ℕ)/(K:ℝ)+(K*r:ℕ)+((r:ℝ)+2)*(L+1)+4*(K+D₀:ℕ)<bV)
    (hbudgetU:(Nr:ℝ)/K+2*(K+D₀:ℕ)<bU)
    (hbudgetS:(Ns*r:ℕ)/(K:ℝ)+(D₀*r:ℕ)+((r:ℝ)+2)*(L+1)+8*(K+D₀:ℕ)<bV) :
    ∃ C:(Fin Nr⊕Fin Ns)→OrdinaryWheel Q F H r,
      (∀ i j,i≠j → Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j))) ∧
      (∀ i,ordinaryWheelResources (C i)∩ordinaryHostResources (spanningRestriction Q I)
        (fun a v=>H a v∧a∈I∧v∈J)=
        {Sum.elim (fun j=>Sum.inl s(x j,y j)) (fun j=>Sum.inr (z j,u j)) i}) ∧
      (∀ a,(wheelFamilyRim C).degree a≤4*(K+D₀)) ∧
      (∀ a,(Finset.univ.filter (fun v=>wheelFamilySpokes C a v)).card≤2*(K+D₀)) ∧
      (∀ v,(Finset.univ.filter (fun a=>wheelFamilySpokes C a v)).card≤(K+D₀)*r) ∧
      (∀i,ordinaryWheelHub (C i)∈J∪B ∧ (ordinaryWheelRim (C i)).support⊆I∪X) :=by
  have hxn:∀ i,x i∉X:=fun i h=>Finset.disjoint_left.mp hIX (hx i) h
  have hyn:∀ i,y i∉X:=fun i h=>Finset.disjoint_left.mp hIX (hy i) h
  have hzn:∀ i,z i∉X:=fun i h=>Finset.disjoint_left.mp hIX (hz i) h
  obtain ⟨R,hR,hRdis,hRcap,hRhcap,hRdeg,hRrow,hRcol⟩:=prescribed_rim_wheel_packing Q F H X B Nr r K D₀ hr hK
    x y hxn hyn hxy hFxy hedge hend L bV bU hL hF
    (fun v hv=>hcount v (Finset.mem_union_right _ hv)) hubs hbudgetR hbudgetU
  let D:=wheelFamilyRim R
  have hcounts (i:Fin Ns) (a c:V):bV-4*(K+D₀:ℕ)≤
      (((X.filter (fun w=>H w (u i)))∩(Q\D).neighborFinset a∩(Q\D).neighborFinset c).card:ℝ):=by
    have hh:(((X.filter (fun w=>H w (u i)))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ)≤
      ((X.filter (fun w=>H w (u i)))∩(Q\D).neighborFinset a∩(Q\D).neighborFinset c).card+D.degree a+D.degree c:=by
      exact_mod_cast two_common_neighbours_after_deletion Q D (X.filter (fun w=>H w (u i))) a c
    have hdA:(D.degree a:ℝ)≤2*(K+D₀:ℕ):=by exact_mod_cast hRdeg a
    have hdC:(D.degree c:ℝ)≤2*(K+D₀:ℕ):=by exact_mod_cast hRdeg c
    linarith only [hh,hdA,hdC,hcount (u i) (Finset.mem_union_left _ (hu i)) a c]
  obtain ⟨S,hS,hSdis,hScap,hSdeg,hSrow,hScol⟩:=prescribed_spoke_wheel_packing (Q\D) F H X Ns r K D₀ hr hK
    z u hzn hH hspoke hsend hshub L (bV-4*(K+D₀:ℕ)) hL hF
    (by intro i a c;convert hcounts i a c using 1 <;> congr!) (by linarith only [hbudgetS])
  let S':Fin Ns→OrdinaryWheel Q F H r:=fun i=>ordinaryWheelInclude sdiff_le (S i)
  let C:(Fin Nr⊕Fin Ns)→OrdinaryWheel Q F H r:=Sum.elim R S'
  have hcross (i:Fin Nr) (j:Fin Ns):Disjoint (ordinaryWheelResources (R i)) (ordinaryWheelResources (S' j)):=by
    apply Finset.disjoint_left.mpr
    intro e heR heS
    cases e with
    | inl e =>
      rw [ordinaryWheelResources_rim] at heR heS
      induction e using Sym2.inductionOn with
      | _ a c =>
        have hDac:D.Adj a c:=SimpleGraph.iSup_adj.mpr ⟨i,heR⟩
        exact ((S j).val.1.property heS).2 hDac
    | inr av =>
      rw [ordinaryWheelResources_spoke] at heR heS
      have hhub:ordinaryWheelHub (R i)=u j:=heR.1.trans (heS.1.symm.trans (hS j).1)
      exact Finset.disjoint_left.mp hJB (hu j) (hhub ▸ (hR i).1)
  have hcapR (a:V):wheelRimLoad R a≤K+D₀:=by
    by_cases ha:a∈X
    · exact (hRcap a ha).trans (Nat.le_add_right _ _)
    · apply le_trans _ ((hend a).trans (Nat.le_add_left _ _))
      apply Finset.card_le_card
      intro i hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      rcases (hR i).2.2 a (Finset.mem_filter.mp hi).2 with h|h|h
      · exact Or.inl h
      · exact Or.inr h
      · exact (ha h).elim
  have hcapS (a:V):wheelRimLoad S a≤K+D₀:=by
    by_cases ha:a∈X
    · exact (hScap a ha).trans (Nat.le_add_right _ _)
    · apply le_trans _ ((hsend a).trans (Nat.le_add_left _ _))
      apply Finset.card_le_card
      intro i hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      rcases (hS i).2.2 a (Finset.mem_filter.mp hi).2 with h|h
      · exact h
      · exact (ha h).elim
  have hcap (a:V):wheelRimLoad C a≤2*(K+D₀):=by
    have he:wheelRimLoad C a=wheelRimLoad R a+wheelRimLoad S a:=by
      simp only [wheelRimLoad,Finset.card_filter,Fintype.sum_sum_type,C,Sum.elim_inl,Sum.elim_inr]
      rfl
    rw [he]
    have hh:=Nat.add_le_add (hcapR a) (hcapS a)
    omega
  have hhubS (v:U):wheelHubLoad S v≤D₀:=by
    have he:wheelHubLoad S v=(Finset.univ.filter (fun i=>u i=v)).card:=by
      unfold wheelHubLoad
      congr 1;ext i;simp only [Finset.mem_filter,Finset.mem_univ,true_and,show ordinaryWheelHub (S i)=u i from (hS i).1]
    rw [he];exact hshub v
  have hhubC (v:U):wheelHubLoad C v≤K+D₀:=by
    have he:wheelHubLoad C v=wheelHubLoad R v+wheelHubLoad S v:=by
      simp only [wheelHubLoad,Finset.card_filter,Fintype.sum_sum_type,C,Sum.elim_inl,Sum.elim_inr]
      rfl
    rw [he]
    exact Nat.add_le_add (hRhcap v) (hhubS v)
  refine ⟨C,?_,?_,?_,?_,?_,?_⟩
  · intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j=>exact hRdis i j (fun h=>hij (congrArg Sum.inl h))
      | inr j=>exact hcross i j
    | inr i =>
      cases j with
      | inl j=>exact (hcross j i).symm
      | inr j=>exact hSdis i j (fun h=>hij (congrArg Sum.inr h))
  · intro i
    cases i with
    | inl i =>
      exact prescribed_rim_wheel_inner_intersection (R i) I X J hIX (x i) (y i) (hx i) (hy i)
        (hR i).2.1 (fun h=>Finset.disjoint_left.mp hJB h (hR i).1) (hR i).2.2
    | inr i =>
      exact prescribed_spoke_wheel_inner_intersection (S' i) I X J hIX (z i) (u i) (hz i) (hu i)
        (hS i).1 (hS i).2.1 (hS i).2.2
  · intro a
    have hh:=(wheelRimLoad_degree C a).trans (Nat.mul_le_mul_left 2 (hcap a))
    omega
  · intro a;exact (wheelRimLoad_spoke_row C a).trans (hcap a)
  · intro v;exact (wheelHubLoad_spoke_column C v).trans (Nat.mul_le_mul_right r (hhubC v))
  · intro i
    cases i with
    | inl i =>
      refine ⟨Finset.mem_union_right _ (hR i).1,?_⟩
      intro v hv
      change v∈I ∨ v∈X
      rcases (hR i).2.2 v hv with h|h|h
      · exact Or.inl (by simpa [h] using hx i)
      · exact Or.inl (by simpa [h] using hy i)
      · exact Or.inr h
    | inr i =>
      refine ⟨?_,?_⟩
      · change ordinaryWheelHub (S i)∈J∪B
        rw [(hS i).1]
        exact Finset.mem_union_left _ (hu i)
      · intro v hv
        change v∈I ∨ v∈X
        rcases (hS i).2.2 v hv with h|h
        · exact Or.inl (by simpa [h] using hz i)
        · exact Or.inr h

end Oberwolfach
