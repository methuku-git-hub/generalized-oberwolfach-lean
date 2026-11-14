module

public import Oberwolfach.FixedClassRootOrder
public import Oberwolfach.MarkedHubAbsorberAbundance

@[expose] public section

/-! Paired absorber counts for every root set of the fixed class profile.
The root order and actual cycle records are constructed from the cycle and
root-omitted common-path counts; absorber existence is not an input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem class_marked_absorber_counts (m:ℕ) (hm:3<m+1) (β:ℝ) (hβ:0<β):
    ∃ N:ℕ,∀ (V E K:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→
    ∀ (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (b:ℕ) (A B:Finset V),
    Disjoint A B→
    β*(Fintype.card V:ℝ)^(m+1)≤Fintype.card (ClassMarkedCycle tail head ktail khead m π b A B)→
    (∀ j:Bool,∀ v v':V,v≠v'→(if j then v∈A else v∈B)→(if j then v'∈A else v'∈B)→
      β*(Fintype.card V:ℝ)^m≤Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b
        (fun x (_:Unit)=>x∈B) (fun x (_:Unit)=>x∈A) j v v' () ()))→
    ∀ X:Finset V,X⊆A∪B→(X∩A).card=1→(X∩B).card=m→
      (β/2)^(m+2)*(Fintype.card V:ℝ)^((m+1)*(m+1))≤
        Fintype.card (LabelledAbsorberFamily (classMarkedCycleVertices (tail:=tail) (head:=head)
          (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) (A:=A) (B:=B))
          (fun (_:Unit)=>pairedAbsorberTemplate (m+1)) X):=by
  obtain ⟨N,hN⟩:=paired_absorber_order_threshold m β hβ
  refine ⟨N,?_⟩
  intro V E K _ _ hn tail head ktail khead π b A B hAB hbase hpath X hX hXA hXB
  obtain ⟨x,hx,hxset,hxA,hxB⟩:=fixed_class_root_order m A B X hAB hX hXA hXB
  have hcount:=marked_hub_paired_absorber_count (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
    (m:=m) (π:=π) (b:=b) (H₀:=fun x (_:Unit)=>x∈B) (Hₖ:=fun x (_:Unit)=>x∈A)
    hm () x hx ⟨hxA,hxB⟩ β hβ hbase (by
      intro j v v' hne hv hv'
      simpa only [Fintype.card_eq_nat_card] using hpath j v v' hne hv hv') (hN _ hn).1 (hN _ hn).2
  rw [hxset] at hcount
  let R:=classMarkedCycleVertices (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
    (m:=m) (π:=π) (b:=b) (A:=A) (B:=B)
  let embed:LabelledCycleRecord R (pairedAbsorberTemplate (m+1)).val X→
      LabelledAbsorberFamily R (fun (_:Unit)=>pairedAbsorberTemplate (m+1)) X:=fun D=>⟨(),D⟩
  have hi:Function.Injective embed:=by
    intro D E he
    exact eq_of_heq (Sigma.mk.inj_iff.mp he).2
  exact hcount.trans (by exact_mod_cast Fintype.card_le_of_injective embed hi)

end Oberwolfach
