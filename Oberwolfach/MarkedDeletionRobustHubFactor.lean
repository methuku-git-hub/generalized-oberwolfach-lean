module

public import Oberwolfach.MarkedHubFactorAndWheels
public import Oberwolfach.MarkedHubRimDeletionCounts
public import Oberwolfach.MarkedHubRimDeletionWeights
public import Oberwolfach.MarkedPhysicalRimDeletionDegrees

@[expose] public section

/-! A marked factor at a hub after any later bounded-degree physical rim
 deletion. Counts and loads are inherited from the fixed original host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_deletion_robust_hub_factor (m:ℕ) (hm:3≤m) (β bLo B:ℝ)
    (hβ:0<β) (hbLo:0<bLo) (hB:0≤B):
    ∃ θ:ℝ,0<θ∧∃ N:ℕ,1≤N∧∀ (V U E K:Type)
      [Fintype V] [Fintype E] [Fintype K] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V→∀ (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
      (b:ℕ) (H₀ Hₖ:V→U→Prop) (u:U),1≤b→
      Function.Injective (markedPhysicalEdge tail head ktail khead π)→
      (∀ v,¬(H₀ v u∧Hₖ v u))→(∀ v z,H₀ v u→Hₖ z u→v≠π z)→
      β*Fintype.card V≤Fintype.card (hubNeighbourClass H₀ Hₖ u true)→
      Fintype.card (hubNeighbourClass H₀ Hₖ u false)=m*Fintype.card (hubNeighbourClass H₀ Hₖ u true)→
      β*(Fintype.card V:ℝ)^(m+1)≤Fintype.card (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u)→
      (∀ j:Bool,∀ v v':V,v≠v'→(if j then Hₖ v u else H₀ v u)→(if j then Hₖ v' u else H₀ v' u)→
        β*(Fintype.card V:ℝ)^m≤Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b H₀ Hₖ j v v' u u))→
      ∀ w:MarkedCycleTuple tail head ktail khead m π b→ℝ,
      (∀ C,bLo/(Fintype.card V:ℝ)^m≤w C∧w C≤B/(Fintype.card V:ℝ)^m)→
      (∀ v,H₀ v u∨Hₖ v u→|1-hypergraphWeightedDegree (hubMarkedCycleVertices (H₀:=H₀) (Hₖ:=Hₖ) u) (fun C=>w (hubCycleAsMarked u C)) v|≤θ)→
      ∀ D:SimpleGraph V,(∀ v,(D.degree v:ℝ)≤θ*Fintype.card V)→
      let PE:=fun e:E=>¬D.Adj (tail e) (head e)
      let PK:=fun e:K=>¬D.Adj (ktail e) (π (khead e))
      ∃ M:Finset (HubMarkedCycle (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀ Hₖ u),
        (∀ C∈M,∀ Z∈M,C≠Z→Disjoint (hubMarkedCycleVertices u C) (hubMarkedCycleVertices u Z))∧
        M.biUnion (hubMarkedCycleVertices (H₀:=H₀) (Hₖ:=Hₖ) u)=Finset.univ.filter (fun v=>H₀ v u∨Hₖ v u):=by
  let c:ℝ:=(m:ℝ)+1
  have hc:0<c:=by dsimp[c];positivity
  obtain ⟨η,hη,N,hfactor⟩:=marked_hub_factor_and_wheels m (by omega) (β/2) bLo B (by positivity) hbLo hB
  let θ:=min (β/(8*c)) (min (η/2) (η/(20*c^4*(B+1))))
  have hθ:0<θ:=by dsimp[θ];positivity
  have htcount:8*c*θ≤β:=by
    have hh:θ≤β/(8*c):=min_le_left _ _
    convert (le_div_iff₀ (by positivity:0<8*c)).mp hh using 1 <;> ring
  have htη:θ≤η/2:=(min_le_right _ _).trans (min_le_left _ _)
  have htload:θ≤η/(20*c^4*(B+1)):=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨θ,hθ,max N 1,by omega,?_⟩
  intro V U E K _ _ _ _ _ hn tail head ktail khead π b H₀ Hₖ u hb hp hdis hsep hsize hratio hbase hpath w hw herr D hD PE PK
  have hnpos:0<Fintype.card V:=by omega
  have hnR:0<(Fintype.card V:ℝ):=by exact_mod_cast hnpos
  let n:ℝ:=Fintype.card V
  let d:=θ*n
  have hd:0≤d:=by dsimp[d,n];positivity
  obtain ⟨hEout,hEin,hKout,hKin⟩:=marked_physical_rim_deletion_degrees tail head ktail khead π hp D d hD
  have ho:∀ x,(∑ e,if ¬PE e∧tail e=x then (1:ℝ) else 0)≤d:=by simpa only [PE,not_not] using hEout
  have hi:∀ x,(∑ e,if ¬PE e∧head e=x then (1:ℝ) else 0)≤d:=by simpa only [PE,not_not] using hEin
  have hko:∀ x,(∑ e,if ¬PK e∧ktail e=x then (1:ℝ) else 0)≤d:=by simpa only [PK,not_not] using hKout
  have hki:∀ x,(∑ e,if ¬PK e∧khead e=x then (1:ℝ) else 0)≤d:=by simpa only [PK,not_not] using hKin
  obtain ⟨hinj,hkinj⟩:=markedPhysicalEdge_endpoint_injections tail head ktail khead π hp
  let w':=fun C:HubMarkedCycle (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
    (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀ Hₖ u=>
    w (markedCycleToLarger PE PK (hubCycleAsMarked u C))
  have hb':(β/2)*n^(m+1)≤Fintype.card (HubMarkedCycle (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀ Hₖ u):=by
    have hloss:=hub_marked_cycle_rim_deletion_count (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ) (by omega:1≤m) PE PK u d hd (by convert ho using 1 <;> congr!) (by convert hko using 1 <;> congr!)
    have hscale:=mul_le_mul_of_nonneg_right htcount (pow_nonneg hnR.le (m+1))
    have he:3*c*d*n^m=3*c*θ*n^(m+1):=by dsimp[d];rw [pow_succ];ring
    change _≤3*c*d*n^m at hloss
    rw [he] at hloss
    change β*n^(m+1)≤_ at hbase
    nlinarith only [hloss,hbase,hscale,mul_nonneg (mul_nonneg hc.le hθ.le) (pow_nonneg hnR.le (m+1))]
  have hp':∀ j:Bool,∀ v v':V,v≠v'→(if j then Hₖ v u else H₀ v u)→(if j then Hₖ v' u else H₀ v' u)→
      (β/2)*n^m≤Fintype.card (RootFirstCommonMarkedPath (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀ Hₖ j v v' u u):=by
    intro j v v' hne hv hv'
    have hloss:=hub_marked_path_rim_deletion_count (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ) (by omega:1≤m) PE PK u j v v' d hd (by convert ho using 1 <;> congr!) (by convert hi using 1 <;> congr!) (by convert hko using 1 <;> congr!) (by convert hki using 1 <;> congr!)
    have hscale:=mul_le_mul_of_nonneg_right htcount (pow_nonneg hnR.le m)
    have he:4*c*d*n^(m-1)=4*c*θ*n^m:=by
      dsimp[d]
      have hpow:n^m=n^(m-1)*n:=by
        calc
          n^m=n^((m-1)+1):=congrArg (fun k:ℕ=>n^k) (by omega)
          _=n^(m-1)*n:=pow_succ _ _
      rw [hpow]
      ring
    change _≤4*c*d*n^(m-1) at hloss
    rw [he] at hloss
    have hh:=hpath j v v' hne hv hv'
    change β*n^m≤_ at hh
    nlinarith only [hh,hloss,hscale]
  have hw0:∀ C,0≤w C∧w C≤B/n^m:=by
    intro C
    exact ⟨(div_pos hbLo (pow_pos hnR _)).le.trans (hw C).1,(hw C).2⟩
  have herr':∀ v,H₀ v u∨Hₖ v u→|1-hypergraphWeightedDegree (hubMarkedCycleVertices (H₀:=H₀) (Hₖ:=Hₖ) u) w' v|≤η:=by
    intro v hv
    have he:=hub_marked_rim_deletion_weight_error hm hnpos u hdis PE PK hinj hkinj w B d hB hd hw0 (by convert ho using 1 <;> congr!) (by convert hi using 1 <;> congr!) (by convert hko using 1 <;> congr!) (by convert hki using 1 <;> congr!) v hv
    have hid:10*c^4*B*d/n=10*c^4*B*θ:=by dsimp[d];field_simp [show n≠0 from ne_of_gt hnR]
    change |hypergraphWeightedDegree (hubMarkedCycleVertices (H₀:=H₀) (Hₖ:=Hₖ) u) w' v-
      hypergraphWeightedDegree (hubMarkedCycleVertices (H₀:=H₀) (Hₖ:=Hₖ) u) (fun C=>w (hubCycleAsMarked u C)) v|≤10*c^4*B*d/n at he
    rw [hid,abs_sub_comm] at he
    have hbound:= (le_div_iff₀ (by positivity:0<20*c^4*(B+1))).mp htload
    have he':10*c^4*B*θ≤η/2:=by nlinarith only [hbound,mul_nonneg (pow_nonneg hc.le 4) hθ.le]
    have hh:=abs_sub_le (1:ℝ)
      (hypergraphWeightedDegree (hubMarkedCycleVertices (H₀:=H₀) (Hₖ:=Hₖ) u) (fun C=>w (hubCycleAsMarked u C)) v)
      (hypergraphWeightedDegree (hubMarkedCycleVertices (H₀:=H₀) (Hₖ:=Hₖ) u) w' v)
    exact hh.trans ((add_le_add (herr v hv) he).trans (by linarith only [htη,he']))
  obtain ⟨M,hM,hunion,_⟩:=hfactor V U {e // PE e} {e // PK e} (by omega)
    (fun e=>tail e.val) (fun e=>head e.val) (fun e=>ktail e.val) (fun e=>khead e.val)
    π b H₀ Hₖ u hb (markedRestrictedPhysical_injective PE PK hp) hdis hsep
    (by have hh:=mul_le_mul_of_nonneg_right (show β/2≤β by linarith) hnR.le;exact hh.trans hsize)
    hratio hb' hp' w' (fun C=>hw (markedCycleToLarger PE PK (hubCycleAsMarked u C))) herr'
  exact ⟨M,hM,hunion⟩

end Oberwolfach
