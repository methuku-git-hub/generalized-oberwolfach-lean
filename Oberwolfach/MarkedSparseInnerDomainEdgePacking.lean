module

public import Oberwolfach.MarkedInnerDomainPackingNumerics

@[expose] public section

/-! The sparse inner-edge packing with the tolerance chosen before the
permutation separation radius. The actual free-use cap is ceil(eta*n);
all numerical conditions of both successive constructions are proved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sparse_inner_domain_edge_packing (l:ℕ) (hl:2≤l) (β:ℝ) (hβ:0<β)
    (η:ℝ) (hη:0<η) (hη1:η≤1) (hscale:100*((l:ℝ)+20)*η≤β):
    ∀ b:ℕ,1≤b→∃ n₀:ℕ,
    ∀ (V U E T:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    ∀ (tail head:E→V) (ktail khead:T→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V),n₀≤Fintype.card V→
    Function.Injective (markedPhysicalEdge tail head ktail khead π)→
    ∀ (X:Finset V) (Z:Finset U),(∀ v,π v∈X↔v∈X)→
    (∀ u,∀ t x,β*Fintype.card V≤((X.filter (fun z=>markedArcPresent tail head ktail khead t x z∧
      (if t then HK z u else H₀ z u))).card:ℝ))→
    (∀ u,∀ t x y,x≠(if t then π y else y)→β*Fintype.card V≤((X.filter (fun z=>
      markedArcPresent tail head ktail khead false x z∧
      markedArcPresent tail head ktail khead t z y∧H₀ z u)).card:ℝ))→
    ∀ Nr Ns:ℕ,(Nr:ℝ)≤η^2*(Fintype.card V:ℝ)^2→(Ns:ℝ)≤η^2*(Fintype.card V:ℝ)^2→
    ∀ (x y:Fin Nr→V) (tr:Fin Nr→Bool),(∀ i,x i∉X)→(∀ i,y i∉X)→
    (∀ i,¬PermutationClose π b (x i) (y i))→
    (∀ i,markedArcPresent tail head ktail khead (tr i) (x i) (y i))→
    Function.Injective (fun i=>if tr i then ({x i,π (y i)}:Finset V) else {x i,y i})→
    (∀ a,((Finset.univ.filter (fun i=>a=x i∨a=y i)).card:ℝ)≤η^2*Fintype.card V)→
    (∀ i,β*Fintype.card V≤((Z.filter (fun v=>H₀ (x i) v∧(if tr i then HK (y i) v else H₀ (y i) v))).card:ℝ))→
    ∀ (z:Fin Ns→V) (u:Fin Ns→U) (ts:Fin Ns→Bool),(∀ i,z i∉X)→(∀ i,u i∉Z)→
    (∀ i,if ts i then HK (z i) (u i) else H₀ (z i) (u i))→
    Function.Injective (fun i=>(z i,u i))→
    (∀ a,((Finset.univ.filter (fun i=>a=z i)).card:ℝ)≤η^2*Fintype.card V)→
    (∀ v,((Finset.univ.filter (fun i=>u i=v)).card:ℝ)≤η^2*Fintype.card V)→
    ∃ R:Fin Nr→MarkedWheel tail head ktail khead (l+4) π b H₀ HK,
    ∃ S:Fin Ns→MarkedWheel tail head ktail khead (l+4) π b H₀ HK,
      (∀ i,(markedWheelPhysicalResources (R i)).filter (markedInnerResource (Xᶜ) (Zᶜ))=
        {Sum.inl (if tr i then ({x i,π (y i)}:Finset V) else {x i,y i})})∧
      (∀ i,(markedWheelPhysicalResources (S i)).filter (markedInnerResource (Xᶜ) (Zᶜ))={Sum.inr (z i,u i)})∧
      (∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (R i)) (markedWheelPhysicalResources (R j)))∧
      (∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (S i)) (markedWheelPhysicalResources (S j)))∧
      (∀ i j,Disjoint (markedWheelPhysicalResources (R i)) (markedWheelPhysicalResources (S j)))∧
      (∀ a,((markedFamilyRim R).degree a:ℝ)≤12*η*Fintype.card V)∧
      (∀ a,((markedFamilyRim S).degree a:ℝ)≤12*η*Fintype.card V)∧
      (∀ a,((Finset.univ.filter (markedFamilySpokes R a)).card:ℝ)≤3*η*Fintype.card V)∧
      (∀ a,((Finset.univ.filter (markedFamilySpokes S a)).card:ℝ)≤3*η*Fintype.card V)∧
      (∀ v,((Finset.univ.filter (fun a=>markedFamilySpokes R a v)).card:ℝ)≤2*(l+5)*η*Fintype.card V)∧
      (∀ v,((Finset.univ.filter (fun a=>markedFamilySpokes S a v)).card:ℝ)≤(l+5)*η*Fintype.card V):=by
  intro b hb
  obtain ⟨n₀,hn₀⟩:=marked_inner_domain_order_threshold l β hβ η hη hη1 hscale b
  refine ⟨n₀,?_⟩
  intro V U E T _ _ _ _ tail head ktail khead H₀ HK π hn hphys X Z hX hstep hjoin Nr Ns hNr hNs
    x y tr hx hy hsep hroot hedge hend hhubs z u ts hz hu hspoke hspinj hsrow hscol
  let n:=Fintype.card V
  let K:=Nat.ceil (η*n)
  let D:=Nat.floor (η^2*n)
  obtain ⟨hnpos,hηn,hη1,hscale,hsepn,hKlo,hKhi⟩:=hn₀ n hn
  have hq:0<η*n:=by positivity
  have hK:0<K:=by
    have hh:(0:ℝ)<K:=hq.trans_le hKlo
    exact_mod_cast hh
  have hD:(D:ℝ)≤η*n:=by
    have hf:(D:ℝ)≤η^2*n:=Nat.floor_le (by positivity)
    have he:η^2≤η:=by nlinarith only [hη,hη1]
    exact hf.trans (mul_le_mul_of_nonneg_right he (by positivity))
  have hB:(0:ℝ)<β*n:=by positivity
  have hrn:(Nr:ℝ)≤(η*n)^2:=by convert hNr using 1 <;> dsimp only [n] <;> ring
  have hsn:(Ns:ℝ)≤(η*n)^2:=by convert hNs using 1 <;> dsimp only [n] <;> ring
  have budgets:=marked_inner_domain_packing_numeric_budgets l (η*n) K D D Nr Ns
    (((l:ℝ)+6)*(2*b+1)) (β*n) (by positivity) hq hB hKlo hKhi hD hD hrn hsn hsepn hscale
  have hrbudget:(Nr*(l+5):ℕ)/(K:ℝ)+(K*(l+5):ℕ)+(l+6)*(2*b+1)+8*(K+D:ℕ)<β*n:=by
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using budgets.1
  have hubbudget:Nr/(K:ℝ)+2*(K+D:ℕ)<β*n:=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using budgets.2.1
  have hsbudget:(Ns*(l+5):ℕ)/(K:ℝ)+(D*(l+5):ℕ)+(l+6)*(2*b+1)+
      8*(K+D:ℕ)+8*(K+D:ℕ)<β*n:=by
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using budgets.2.2
  obtain ⟨R,S,hRI,hSI,hRR,hSS,hRS,hRdeg,hSdeg,hRrow,hSrow,hRcol,hScol⟩:=
    marked_inner_prescribed_edge_packing hl hb hphys X Z hX Nr Ns K D D hK x y tr hx hy hsep hroot hedge
      (fun a=>Nat.le_floor (hend a)) z u ts hz hu hspoke hspinj
      (fun a=>Nat.le_floor (hsrow a)) (fun v=>Nat.le_floor (hscol v))
      hstep hjoin hhubs hrbudget hubbudget hsbudget
  have hKD:((K+D:ℕ):ℝ)≤3*(η*n):=by push_cast;linarith only [hKhi,hD]
  refine ⟨R,S,hRI,hSI,hRR,hSS,hRS,?_,?_,?_,?_,?_,?_⟩
  · intro a;have hh:((markedFamilyRim R).degree a:ℝ)≤4*(K+D:ℕ):=by exact_mod_cast hRdeg a
    nlinarith only [hh,hKD]
  · intro a;have hh:((markedFamilyRim S).degree a:ℝ)≤4*(K+D:ℕ):=by exact_mod_cast hSdeg a
    nlinarith only [hh,hKD]
  · intro a;have hh:((Finset.univ.filter (markedFamilySpokes R a)).card:ℝ)≤(K+D:ℕ):=by exact_mod_cast hRrow a
    nlinarith only [hh,hKD]
  · intro a;have hh:((Finset.univ.filter (markedFamilySpokes S a)).card:ℝ)≤(K+D:ℕ):=by exact_mod_cast hSrow a
    nlinarith only [hh,hKD]
  · intro v;have hh:((Finset.univ.filter (fun a=>markedFamilySpokes R a v)).card:ℝ)≤(K:ℝ)*(l+5):=by exact_mod_cast hRcol v
    have hmul:=mul_le_mul_of_nonneg_right hKhi (show (0:ℝ)≤l+5 by positivity)
    nlinarith only [hh,hmul]
  · intro v;have hh:((Finset.univ.filter (fun a=>markedFamilySpokes S a v)).card:ℝ)≤(D:ℝ)*(l+5):=by exact_mod_cast hScol v
    have hmul:=mul_le_mul_of_nonneg_right hD (show (0:ℝ)≤l+5 by positivity)
    nlinarith only [hh,hmul]

end Oberwolfach
