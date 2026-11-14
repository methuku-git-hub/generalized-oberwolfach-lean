module

public import Oberwolfach.MarkedPrescribedRimPacking
public import Oberwolfach.MarkedPrescribedSpokePacking
public import Oberwolfach.MarkedInnerResources
public import Oberwolfach.MarkedSpokeDeletionExtensions
public import Oberwolfach.MarkedFamilyRestrictionLift

@[expose] public section

/-! Complete prescribed inner rim edges and spokes in one marked host.
The spoke stage is performed after deleting the actual rim-stage wheels;
its extension bounds are derived from the resulting physical and spoke
losses. Both stages have exactly their prescribed inner intersections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 26000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:T→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_prescribed_inner_edge_packing
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b (l+1) c ch)
    (hl:2≤l) (hb:1≤b) (hphys:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (X:Finset V) (J:Finset U) (hX:∀ v,π v∈X↔v∈X)
    (Nr Ns K Dr Ds:ℕ) (hK:0<K)
    (x y:Fin Nr→V) (tr:Fin Nr→Bool) (hx:∀ i,x i∉X) (hy:∀ i,y i∉X)
    (hsep:∀ i,¬PermutationClose π b (x i) (y i))
    (hroot:∀ i,markedArcPresent tail head ktail khead (tr i) (x i) (y i))
    (hedge:Function.Injective (fun i=>if tr i then ({x i,π (y i)}:Finset V) else {x i,y i}))
    (hend:∀ a,(Finset.univ.filter (fun i=>a=x i∨a=y i)).card≤Dr)
    (z:Fin Ns→V) (u:Fin Ns→U) (ts:Fin Ns→Bool) (hz:∀ i,z i∉X) (hu:∀ i,u i∈J)
    (hspoke:∀ i,if ts i then HK (z i) (u i) else H₀ (z i) (u i))
    (hspinj:Function.Injective (fun i=>(z i,u i)))
    (hsrow:∀ a,(Finset.univ.filter (fun i=>a=z i)).card≤Ds)
    (hscol:∀ v,(Finset.univ.filter (fun i=>u i=v)).card≤Ds)
    (hbudgetR:((Xᶜ).card:ℝ)+(Nr*(l+5):ℕ)/(K:ℝ)+(l+6)*(2*b+1)+8*(K+Dr:ℕ)<c)
    (hbudgetU:(J.card:ℝ)+Nr/(K:ℝ)+(l+5)*(K+Dr:ℕ)<ch)
    (hbudgetS:((Xᶜ).card:ℝ)+(Ns*(l+5):ℕ)/(K:ℝ)+(Ds*(l+5):ℕ)+(l+6)*(2*b+1)+
      8*(K+Ds:ℕ)+8*(K+Dr:ℕ)+2*(K*(l+5):ℕ)<c):
    ∃ R:Fin Nr→MarkedWheel tail head ktail khead (l+4) π b H₀ HK,
    ∃ S:Fin Ns→MarkedWheel tail head ktail khead (l+4) π b H₀ HK,
      (∀ i,(markedWheelPhysicalResources (R i)).filter (markedInnerResource (Xᶜ) J)=
        {Sum.inl (if tr i then ({x i,π (y i)}:Finset V) else {x i,y i})})∧
      (∀ i,(markedWheelPhysicalResources (S i)).filter (markedInnerResource (Xᶜ) J)={Sum.inr (z i,u i)})∧
      (∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (R i)) (markedWheelPhysicalResources (R j)))∧
      (∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (S i)) (markedWheelPhysicalResources (S j)))∧
      (∀ i j,Disjoint (markedWheelPhysicalResources (R i)) (markedWheelPhysicalResources (S j)))∧
      (∀ a,(markedFamilyRim R).degree a≤4*(K+Dr))∧(∀ a,(markedFamilyRim S).degree a≤4*(K+Ds))∧
      (∀ a,(Finset.univ.filter (markedFamilySpokes R a)).card≤K+Dr)∧
      (∀ a,(Finset.univ.filter (markedFamilySpokes S a)).card≤K+Ds)∧
      (∀ v,(Finset.univ.filter (fun a=>markedFamilySpokes R a v)).card≤K*(l+5))∧
      (∀ v,(Finset.univ.filter (fun a=>markedFamilySpokes S a v)).card≤Ds*(l+5)):=by
  have Q₀:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch:=
    ⟨Q.outgoing,Q.incoming,Q.twoOutgoing,Q.twoIncoming,Q.twoStep,
      fun A B hd hn hs=>Q.hubs A B hd (by omega) hs⟩
  obtain ⟨R,hR,hRR,hRcap,hRhub,hRdeg,hRrow,hRcol⟩:=marked_prescribed_rim_wheel_packing Q₀ hl hb hphys
    X J Nr K Dr hK x y tr hx hy hsep hroot hedge hend hbudgetR hbudgetU
  let D:=markedFamilyRim R
  have hD:∀ a,(D.degree a:ℝ)≤4*(K+Dr:ℕ):=by intro a;exact_mod_cast hRdeg a
  have Q₁:=marked_host_extensions_after_rim_deletion Q D (4*(K+Dr:ℕ)) (by positivity) hD
  have Q₂:=marked_host_extensions_after_spoke_deletion Q₁ (markedFamilySpokes R) (K+Dr) (K*(l+5)) hRrow hRcol
  have hsp:∀ i,if ts i then HK (z i) (u i)∧¬markedFamilySpokes R (z i) (u i)
      else H₀ (z i) (u i)∧¬markedFamilySpokes R (z i) (u i):=by
    intro i
    have ha:¬markedFamilySpokes R (z i) (u i):=by
      rintro ⟨j,hju,hzj⟩
      exact (hR j).1 (hju ▸ hu i)
    cases ht:ts i <;> simpa only [ht,Bool.false_eq_true,ite_false,ite_true] using And.intro (hspoke i) ha
  have hbs:((Xᶜ).card:ℝ)+(Ns*((l+1)+4):ℕ)/(K:ℝ)+(Ds*((l+1)+4):ℕ)+
      (((l+1:ℕ):ℝ)+5)*(2*b+1)+8*(K+Ds:ℕ)<c-2*(4*(K+Dr:ℕ))-2*(K*(l+5):ℕ):=by
    push_cast at hbudgetS ⊢
    ring_nf at hbudgetS ⊢
    linarith only [hbudgetS]
  obtain ⟨A,hA,hAA,hAcap,hAdeg,hArow,hAcol⟩:=marked_prescribed_spoke_wheel_packing Q₂ (by omega) hb
    X Ns K Ds hK z u ts hz hsp hspinj hsrow hscol hbs
  have hlift (i:Fin Ns):=marked_family_restriction_lift (by omega) hb R (A i)
  choose S hS using hlift
  have hSv (i):markedWheelRows (S i)=markedWheelRows (A i):=by
    unfold markedWheelRows;rw [(hS i).1]
  have hSu (i):(S i).2.val=(A i).2.val:=(hS i).2.1
  have hSe (i):markedWheelPhysicalResources (S i)=markedWheelPhysicalResources (A i):=(hS i).2.2.1
  have hSS:∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (S i)) (markedWheelPhysicalResources (S j)):=by
    intro i j hij;rw [hSe,hSe];exact hAA i j hij
  have hSrim:markedFamilyRim S=markedFamilyRim A:=by
    apply iSup_congr
    intro i
    ext v w
    have he:({v,w}:Finset V)∈markedCyclePhysicalEdges tail head ktail khead (l+4) π b (S i).1↔
        ({v,w}:Finset V)∈markedCyclePhysicalEdges _ _ _ _ (l+4) π b (A i).1:=by
      have hh:=iff_of_eq (congrArg (fun F=>Sum.inl ({v,w}:Finset V)∈F) (hSe i))
      simpa only [markedWheelPhysicalResources_rim] using hh
    exact and_congr_right (fun _=>he)
  have hSsp (a:V) (v:U):markedFamilySpokes S a v↔markedFamilySpokes A a v:=by
    simp only [markedFamilySpokes,hSu,hSv]
  have hI:∀ v,π v∈Xᶜ↔v∈Xᶜ:=by intro v;simpa only [Finset.mem_compl] using not_congr (hX v)
  refine ⟨R,S,?_,?_,hRR,hSS,fun i j=>(hS j).2.2.2 i,hRdeg,?_,hRrow,?_,hRcol,?_⟩
  · intro i
    refine marked_rim_root_inner_resources (Xᶜ) J hI (R i) _ ?_ (hR i).2.1 (hR i).1 ?_
    · cases ht:tr i <;> simp only [Bool.false_eq_true,ite_false,ite_true,Finset.insert_subset_iff,
        Finset.singleton_subset_iff,Finset.mem_compl,hX,hx i,hy i,not_false_eq_true,and_self]
    · intro a ha hb
      exact (hR i).2.2.2 a (Finset.mem_compl.mp ha) (Finset.mem_compl.mp hb)
  · intro i
    have hc:∀ a∈markedWheelRows (S i),a∈Xᶜ→a=z i:=by
      intro a ha hax
      rw [hSv] at ha
      rcases (hA i).2.2 a ha with h|h
      · exact h
      · exact (Finset.mem_compl.mp hax h).elim
    have he:=marked_one_root_inner_resources (by omega) (Xᶜ) J hI (S i) (z i)
      (Finset.mem_compl.mpr (hz i)) (by rw [hSv];exact (hA i).2.1)
      (by rw [hSu,(hA i).1];exact hu i) hc
    simpa only [hSu,(hA i).1] using he
  · intro a;rw [hSrim];exact hAdeg a
  · intro a
    have he:Finset.univ.filter (markedFamilySpokes S a)=Finset.univ.filter (markedFamilySpokes A a):=by
      ext v;simp only [Finset.mem_filter,hSsp]
    rw [he];exact hArow a
  · intro v
    have he:Finset.univ.filter (fun a=>markedFamilySpokes S a v)=Finset.univ.filter (fun a=>markedFamilySpokes A a v):=by
      ext a;simp only [Finset.mem_filter,hSsp]
    rw [he];exact hAcol v

end Oberwolfach
