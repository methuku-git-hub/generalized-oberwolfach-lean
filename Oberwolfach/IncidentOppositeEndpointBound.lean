module

public import Oberwolfach.MarkedBalanceTestSets

@[expose] public section

/-! Incident occurrences with the opposite endpoint in a specified set.
The factor two records orientation; the finite tag records edge type. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem incident_opposite_endpoint_bound {A D V:Type} [Fintype D] [DecidableEq D] [DecidableEq V]
    (tag:A→D) (tail head:A→V) (hinj:Function.Injective (fun a=>(tag a,tail a,head a)))
    (S:Finset A) (r:V) (X:Finset V) (hS:∀ a∈S,tail a=r∨head a=r):
    (S.filter (fun a=>(if tail a=r then head a else tail a)∈X)).card≤
      2*Fintype.card D*X.card:=by
  classical
  let T:=S.filter (fun a=>(if tail a=r then head a else tail a)∈X)
  let f:=fun a:A=>(tag a,decide (tail a=r),if tail a=r then head a else tail a)
  have hf:Set.InjOn f T:=by
    intro a ha b hb hab
    have ha':=hS a (Finset.mem_filter.mp ha).1
    have hb':=hS b (Finset.mem_filter.mp hb).1
    have he0:tag a=tag b:=congrArg Prod.fst hab
    have he1:decide (tail a=r)=decide (tail b=r):=congrArg (fun z=>z.2.1) hab
    have he2:(if tail a=r then head a else tail a)=(if tail b=r then head b else tail b):=
      congrArg (fun z=>z.2.2) hab
    apply hinj
    by_cases hat:tail a=r
    · have hbt:tail b=r:=by simpa only [hat,decide_true,true_eq_decide_iff] using he1
      simpa only [hat,hbt,ite_true,Prod.mk.injEq,true_and,and_true] using And.intro he0 he2
    · have hbt:tail b≠r:=by simpa only [hat,decide_false,false_eq_decide_iff] using he1
      have hah:head a=r:=ha'.resolve_left hat
      have hbh:head b=r:=hb'.resolve_left hbt
      simpa only [hat,hbt,ite_false,hah,hbh,Prod.mk.injEq,true_and,and_true] using And.intro he0 he2
  have hsub:T.image f⊆Finset.univ.product (Finset.univ.product X):=by
    intro z hz
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hz
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_product.mpr
      ⟨Finset.mem_univ _,(Finset.mem_filter.mp ha).2⟩⟩
  have hcard:=(Finset.card_le_card hsub)
  rw [Finset.card_image_iff.mpr hf] at hcard
  apply hcard.trans_eq
  simp [Finset.card_product, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem marked_balance_inner_term_card {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [DecidableEq V] [DecidableEq U]
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (X:Finset V) (Z:Finset U) (r:V⊕U) (j:Fin 6):
    ((markedBalanceTermSet tail head ktail khead H₀ HK r j).filter (fun a=>
      (if markedActiveAuxTail tail ktail H₀ HK a=r then markedActiveAuxHead head khead H₀ HK a
        else markedActiveAuxTail tail ktail H₀ HK a)∈ordinaryInnerVertices X Z)).card≤
      6*(ordinaryInnerVertices X Z).card:=by
  classical
  have hh:=incident_opposite_endpoint_bound (markedActiveDirectionTag (E:=E) (K:=K) H₀ HK)
    (markedActiveAuxTail tail ktail H₀ HK) (markedActiveAuxHead head khead H₀ HK)
    (markedActive_typed_endpoints_injective tail head ktail khead π H₀ HK hp)
    (markedBalanceTermSet tail head ktail khead H₀ HK r j) r (ordinaryInnerVertices X Z)
    (markedBalanceTermSet_incident tail head ktail khead H₀ HK r j)
  convert hh using 1 <;> norm_num <;> congr!
end Oberwolfach
