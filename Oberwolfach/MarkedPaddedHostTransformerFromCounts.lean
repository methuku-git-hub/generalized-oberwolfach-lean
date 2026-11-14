module

public import Oberwolfach.MarkedPaddedHostTransformer
public import Oberwolfach.MarkedHostExtensionCounts
public import Oberwolfach.MarkedCommonPairCycleProfiles

@[expose] public section

/-! Apply the padded transformer using the uniform row-pattern counts
and the original ordered-pair cycle profiles. Every count substitution
uses distinct paired row roots; no equal-endpoint connector is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_padded_host_transformer_from_counts (l:ℕ) (hl:2≤l)
    (q₀ β blo bhi:ℝ) (hq₀:0<q₀) (hβ:0<β) (hblo:0<blo) (hbhi:0<bhi):
    ∃ ε:ℝ,0<ε∧∀ s:ℕ,∃ t:ℕ,1≤t∧∀ F₀ dF:ℝ,0≤F₀→0≤dF→∃ N:ℕ,
    ∀ (V U E K A S:Type) [Fintype V] [Fintype U] [Fintype A] [Fintype S]
      [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S],
    N≤Fintype.card V→Fintype.card S≤s→
    ∀ (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V) (b:ℕ),1≤b→
    ∀ (src dst:A→V) (row:S→V) (φ:V→V) (u u':S→U) (jr:A→Bool) (js:S→Bool)
      (W R R':Finset V) (B:Finset U) (c ch:ℝ),
    ∀ (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch),
    ∀(hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hRR:Disjoint R R')
    (hroots:∀ e,src e∈R∧dst e∈R∧φ (src e)∈R'∧φ (dst e)∈R')
    (hsroots:∀ s,row s∈R∧φ (row s)∈R') (hU:∀ s,u s∈B∧u' s∈B)
    (hvw:∀ e,¬PermutationClose π b (src e) (dst e))
    (hvw':∀ e,¬PermutationClose π b (φ (src e)) (φ (dst e)))
    (hfour:∀ e,∀ x∈({src e,dst e,φ (src e),φ (dst e)}:Finset V),
      ∀ y∈({src e,dst e,φ (src e),φ (dst e)}:Finset V),x≠y→¬PermutationClose π b x y)
    (hbal:∀ v,Fintype.card {e:A // dst e=v}=Fintype.card {e:A // src e=v}∧
      Fintype.card {e:A // dst e=v}=Fintype.card {s:S // row s=v})
    (hmark:∀ v,(Finset.univ.filter (fun e:{e:A // dst e=v}=>jr e.val=true)).card=
      (Finset.univ.filter (fun s:{s:S // row s=v}=>js s.val=true)).card)
    (hpad:∀ v,¬(Fintype.card {e:A // dst e=v}=1∧
      (Finset.univ.filter (fun e:{e:A // dst e=v}=>jr e.val=true)).card=1))
    (hr:Function.Injective (fun e=>if jr e then ({src e,π (dst e)}:Finset V) else {src e,dst e}))
    (hr':Function.Injective (fun e=>if jr e then ({φ (src e),π (φ (dst e))}:Finset V) else {φ (src e),φ (dst e)}))
    (hs:Function.Injective (fun s=>(row s,u s))) (hs':Function.Injective (fun s=>(φ (row s),u' s)))
    (hroot:∀ e,if jr e then (∃ k,ktail k=src e∧khead k=dst e)∧(∃ k,ktail k=φ (src e)∧khead k=φ (dst e))
      else (∃ k,tail k=src e∧head k=dst e)∧(∃ k,tail k=φ (src e)∧head k=φ (dst e)))
    (hsroot:∀ s,if js s then HK (row s) (u s)∧HK (φ (row s)) (u' s) else H₀ (row s) (u s)∧H₀ (φ (row s)) (u' s))
    (hhbudget:B.card+Fintype.card A<ch)
    (hbudget:W.card+(2*((Fintype.card A:ℝ)*(l+3)+Fintype.card S*(l+4))+
      2*Fintype.card A*(l+4)+(R∪R').card+l+5)*(2*b+1)<c),
    ∀ (ψ:U→U) (F:SimpleGraph V),
    (∀ a,u' a=ψ (u a))→(∀ a,u a≠u' a)→
    (∀ z,(Finset.univ.filter (fun a:{a:S // u a=z}=>js a.val=false)).card=
      (l+4)*(Finset.univ.filter (fun a:{a:S // u a=z}=>js a.val=true)).card)→
    (W.card:ℝ)+((R∪R').card+(Fintype.card A:ℝ)*(l+3)+Fintype.card S*(l+4)+2*Fintype.card A*(l+4))*(dF+1)≤ε*Fintype.card V+F₀→
    (∀ v z,HK v z→¬H₀ v z)→(∀ v,(F.degree v:ℝ)≤dF)→
    MarkedCommonPairCycleProfiles tail head ktail khead H₀ HK π b l q₀ β blo bhi ε→
    ∃ X Y T,∃ H:Finset U,
      X.card≤(R∪R').card+Fintype.card A*(l+3)+Fintype.card S*(l+4)+2*Fintype.card A*(l+4)∧
      (R∪R')⊆X∧
      Disjoint (X\(R∪R')) W∧
      (∀ x∈X\(R∪R'),∀ y∈R∪R',¬PermutationClose π b x y)∧
      (∀ x∈X\(R∪R'),∀ y∈X\(R∪R'),x≠y→¬PermutationClose π b x y)∧
      Disjoint Y (W∪X)∧Y.card≤s*((l+5)*t)∧
      (∀ x∈Y,∀ y∈Y,¬F.Adj x y)∧(∀ x∈Y,∀ y∈X,¬F.Adj x y)∧
      IsResourceTransformer (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
        (m:=l+4) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK))
        (markedRootGraphResources π src dst row jr u)
        (markedRootGraphResources π (fun a=>φ (src a)) (fun a=>φ (dst a)) (fun a=>φ (row a)) jr u') T∧
      (∀ e∈T,MarkedResourceSupported tail head ktail khead π (X∪Y) e)∧
      (∀ e∈T,¬MarkedOldResource tail head ktail khead π (R∪R') B e)∧
      H.card≤2*Fintype.card S+Fintype.card A∧
      (∀ v z,Sum.inr (v,z)∈T→z∈H)∧
      ∀ z∈H,z∈B→∃ a:S,u a=z∨u' a=z :=by
  obtain ⟨ε,hε,hchoose⟩:=marked_padded_host_transformer l hl q₀ β blo bhi hq₀ hβ hblo hbhi
  refine ⟨ε,hε,?_⟩
  intro s
  obtain ⟨t,ht,hchoose⟩:=hchoose s
  refine ⟨t,ht,?_⟩
  intro F₀ dF hF₀ hdF
  obtain ⟨N,hchoose⟩:=hchoose F₀ dF hF₀ hdF
  refine ⟨N,?_⟩
  intro V U E K A S _ _ _ _ _ _ _ _ hn hsbound tail head ktail khead H₀ HK π b hb src dst row φ u u' jr js W R R' B c ch
    Q hp hRR hroots hsroots hU hvw hvw' hfour hbal hmark hpad hr hr' hs hs' hroot hsroot hhbudget hbudget
    ψ F hu' hune hhubbal hnum htypes hF P
  have hne:∀ x∈R,∀ y∈R',x≠y:=by
    intro x hx y hy he
    exact Finset.disjoint_left.mp hRR hx (he.symm ▸ hy)
  have hu:∀ z,(∃ a:S,u a=z)→z≠ψ z:=by
    rintro z ⟨a,rfl⟩;rw [←hu' a];exact hune a
  refine hchoose V U E K A S hn hsbound tail head ktail khead H₀ HK π b hb src dst row φ u u' jr js W R R' B c ch
    hp hRR hroots hsroots hU hvw hvw' hfour hbal hmark hpad hr hr' hs hs' hroot
    ?_ ?_ ?_ ?_ hsroot ?_ ?_ ?_ ?_ ?_ ?_ Q.hubs hhbudget hbudget
    ψ F (fun z=>P.A z (ψ z)) (fun z=>P.B z (ψ z)) (fun z=>P.q z (ψ z))
    hu' hune hhubbal hnum htypes hF
    (fun z hz=>P.q_lower z (ψ z) (hu z hz))
    (fun z hz=>P.marked_class z (ψ z) (hu z hz))
    (fun z hz=>P.ordinary_class z (ψ z) (hu z hz))
    (fun z hz=>P.marked_size z (ψ z) (hu z hz))
    (fun z hz=>P.ordinary_size z (ψ z) (hu z hz))
    (fun z hz=>P.overlap z (ψ z) (hu z hz))
    (fun z hz=>P.cycles z (ψ z) (hu z hz))
    (fun z hz=>P.paths z (ψ z) (hu z hz))
    (fun z=>P.w z (ψ z))
    (fun z hz=>P.weight_bounds z (ψ z) (hu z hz))
    (fun z hz=>P.root_loads z (ψ z) (hu z hz))
  · intro a
    simpa [markedArcPresent,markedSpokesTo] using
      Q.twoOutgoing false (dst a) (φ (dst a)) ∅ (hne _ (hroots a).2.1 _ (hroots a).2.2.2) (by simp)
  · intro a
    simpa [markedArcPresent,markedSpokesTo] using
      Q.twoIncoming false false (src a) (φ (src a)) ∅ (hne _ (hroots a).1 _ (hroots a).2.2.1) (by simp)
  · intro j x
    simpa [markedArcPresent,markedSpokesTo] using Q.outgoing j false x ∅ (by simp)
  · intro x y hxy
    simpa [markedArcPresent,markedSpokesTo] using Q.twoStep false x y ∅ hxy (by simp)
  · intro a
    simpa [markedArcPresent,markedSpokesTo,and_assoc] using
      Q.twoOutgoing false (row a) (φ (row a)) {u a,u' a} (hne _ (hsroots a).1 _ (hsroots a).2) (by simpa using Finset.card_insert_le (u a) {u' a})
  · intro a
    have hh:=Q.twoIncoming (js a) false (row a) (φ (row a)) {u a,u' a}
      (hne _ (hsroots a).1 _ (hsroots a).2) (by simpa using Finset.card_insert_le (u a) {u' a})
    cases hj:js a <;> simpa [markedArcPresent,markedSpokesTo,hj,and_assoc] using hh
  · intro a j x
    have hh:=Q.outgoing j j x {u a,u' a} (by simpa using Finset.card_insert_le (u a) {u' a})
    cases j <;> simpa [markedArcPresent,markedSpokesTo] using hh
  · intro a x y hxy
    simpa [markedArcPresent,markedSpokesTo,and_assoc] using Q.twoStep false x y {u a,u' a} hxy (by simpa using Finset.card_insert_le (u a) {u' a})
  · intro z j x
    have hh:=Q.outgoing j j x {z} (by simp)
    cases j <;> simpa [markedArcPresent,markedSpokesTo] using hh
  · intro z x y hxy
    simpa [markedArcPresent,markedSpokesTo,and_assoc] using Q.twoStep false x y {z} hxy (by simp)

end Oberwolfach
