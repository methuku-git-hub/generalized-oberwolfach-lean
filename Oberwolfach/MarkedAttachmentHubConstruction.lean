module

public import Oberwolfach.MarkedActualAttachments
public import Oberwolfach.MarkedAssignedAttachmentRows
public import Oberwolfach.MarkedRimWheelHubs

@[expose] public section

/-! The rim-hub choice with the four requests calculated from the actual
rim and spoke endpoints. The requests are not supplied as arbitrary sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
  [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S]

theorem marked_actual_attachment_rows (n:ℕ) (src dst:A→V) (row:S→V)
    (a:∀ v,{e:A // dst e=v}≃{s:S // row s=v})
    (d:∀ v,{e:A // src e=v}≃{s:S // row s=v})
    (pr:A→(Fin (n+1)↪V)) (ps:S→(Fin (n+2)↪V)) (P:Finset V)
    (hrP:∀ e k,pr e k∈P) (hsP:∀ s k,ps s k∈P):
    ∀ z:Σ v,DirectedIncidence src dst v,
      markedAttachmentFirst n a d (fun e=>pr e) (fun s=>ps s) z∈P∧
      markedAttachmentLast n a d (fun e=>pr e) (fun s=>ps s) z∈P:=by
  rintro ⟨v,z⟩
  cases z with
  | inl e=>exact ⟨hrP e.val 0,hsP (a v e).val (Fin.last _)⟩
  | inr e=>exact ⟨hsP (d v e).val 0,hrP e.val (Fin.last _)⟩

theorem marked_actual_attachment_ownership (n:ℕ) (src dst:A→V) (row:S→V)
    (a:∀ v,{e:A // dst e=v}≃{s:S // row s=v})
    (d:∀ v,{e:A // src e=v}≃{s:S // row s=v})
    (pr:A→(Fin (n+1)↪V)) (ps:S→(Fin (n+2)↪V))
    (hr:∀ e f,e≠f→Disjoint (Finset.univ.image (pr e)) (Finset.univ.image (pr f)))
    (hrs:∀ e s,Disjoint (Finset.univ.image (pr e)) (Finset.univ.image (ps s))):
    ∀ z:Σ v,DirectedIncidence src dst v,∀ e,
      markedAttachmentFirst n a d (fun e=>pr e) (fun s=>ps s) z∈Finset.univ.image (pr e)∨
      markedAttachmentLast n a d (fun e=>pr e) (fun s=>ps s) z∈Finset.univ.image (pr e)→
      e=directedIncidenceEdge z.2:=by
  have own (e f:A) (k:Fin (n+1)) (hh:pr f k∈Finset.univ.image (pr e)):e=f:=by
    by_contra hne
    exact Finset.disjoint_left.mp (hr e f hne) hh (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩)
  rintro ⟨v,z⟩ e hh
  cases z with
  | inl z=>
    rcases hh with hh|hh
    · exact own e z.val 0 hh
    · exact False.elim (Finset.disjoint_left.mp (hrs e (a v z).val) hh
        (Finset.mem_image.mpr ⟨Fin.last _,Finset.mem_univ _,rfl⟩))
  | inr z=>
    rcases hh with hh|hh
    · exact False.elim (Finset.disjoint_left.mp (hrs e (d v z).val) hh
        (Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩))
    · exact own e z.val (Fin.last _) hh

theorem marked_attachment_hub_construction
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V) (b n:ℕ)
    (src dst:A→V) (row:S→V) (f:V→V) (hloop:∀ e,dst e≠src e)
    (a:∀ v,{e:A // dst e=v}≃{s:S // row s=v})
    (d:∀ v,{e:A // src e=v}≃{s:S // row s=v})
    (τ:∀ v,Equiv.Perm (DirectedIncidence src dst v)) (hτ:∀ v i,τ v i≠i)
    (pr:A→(Fin (n+1)↪V)) (ps:S→(Fin (n+2)↪V)) (ρ:A→Equiv.Perm (Fin (n+3)))
    (C D:A→MarkedCycleTuple tail head ktail khead (n+2) π b)
    (hC:∀ i k,(C i).val k=Fin.cons (α:=fun _=>V) (src i) (Fin.cons (dst i) (pr i)) (ρ i k))
    (hD:∀ i k,(D i).val k=Fin.cons (α:=fun _=>V) (f (src i)) (Fin.cons (f (dst i)) (pr i)) (ρ i k))
    (R P:Finset V) (B:Finset U) (c:ℝ)
    (hroots:∀ i,src i∈R∧dst i∈R∧f (src i)∈R∧f (dst i)∈R)
    (hcross:∀ i,src i≠f (src i)∧src i≠f (dst i)∧dst i≠f (src i)∧dst i≠f (dst i))
    (hrP:∀ i k,pr i k∈P) (hsP:∀ i k,ps i k∈P) (hPR:Disjoint P R)
    (hPP:∀ x∈P,∀ y∈P,x≠y→¬PermutationClose π b x y)
    (hsepPR:∀ x∈P,∀ y∈R,¬PermutationClose π b x y)
    (hRR:∀ i,∀ x∈({src i,dst i,f (src i),f (dst i)}:Finset V),
      ∀ y∈({src i,dst i,f (src i),f (dst i)}:Finset V),x≠y→¬PermutationClose π b x y)
    (hr:∀ e g,e≠g→Disjoint (Finset.univ.image (pr e)) (Finset.univ.image (pr g)))
    (hrs:∀ e s,Disjoint (Finset.univ.image (pr e)) (Finset.univ.image (ps s)))
    (hcount:∀ A Q:Finset V,Disjoint A Q→A.card+Q.card≤n+9→
      (∀ x∈A∪Q,∀ y∈A∪Q,x≠y→¬PermutationClose π b x y)→
      c≤((Finset.univ.filter (fun u=>(∀ x∈A,H₀ x u)∧∀ x∈Q,HK x u)).card:ℝ))
    (hbudget:B.card+Fintype.card A<c):
    ∃ h:A↪U,∃ RC RD:A→MarkedWheel tail head ktail khead (n+2) π b H₀ HK,
      (∀ e,h e∉B)∧(∀ e,(RC e).1=C e∧(RD e).1=D e∧(RC e).2.val=h e∧(RD e).2.val=h e)∧
      ∀ z:Σ v,DirectedIncidence src dst v,
        H₀ (markedAttachmentFirst n a d (fun e=>pr e) (fun s=>ps s) z) (h (directedIncidenceEdge (τ z.1 z.2)))∧
        H₀ (markedAttachmentLast n a d (fun e=>pr e) (fun s=>ps s) z) (h (directedIncidenceEdge (τ z.1 z.2))):=by
  let first:=markedAttachmentFirst n a d (fun e=>pr e) (fun s=>ps s)
  let last:=markedAttachmentLast n a d (fun e=>pr e) (fun s=>ps s)
  let T:=markedRimHubAttachmentRows τ first last
  have hown:=marked_actual_attachment_ownership n src dst row a d pr ps hr hrs
  have hTP:∀ e,T e⊆P:=by
    intro e x hx
    simp only [T,markedRimHubAttachmentRows,Finset.mem_insert,Finset.mem_singleton] at hx
    have hh:=marked_actual_attachment_rows n src dst row a d pr ps P hrP hsP
    rcases hx with rfl|rfl|rfl|rfl
    · exact (hh _).1
    · exact (hh _).2
    · exact (hh _).1
    · exact (hh _).2
  have hTpr:=marked_assigned_attachment_rows_avoid_rim_path τ hτ hloop first last
    (fun e=>Finset.univ.image (pr e)) hown
  have hTex:∀ e,Disjoint (T e) (Finset.univ.image (C e).val∪Finset.univ.image (D e).val):=by
    intro e
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hc:(C e).val=fun k=>Fin.cons (α:=fun _=>V) (src e) (Fin.cons (dst e) (pr e)) (ρ e k):=funext (hC e)
    have hd:(D e).val=fun k=>Fin.cons (α:=fun _=>V) (f (src e)) (Fin.cons (f (dst e)) (pr e)) (ρ e k):=funext (hD e)
    rw [hc,hd,two_root_cycle_pair_image] at hy
    rcases Finset.mem_union.mp hy with hy|hy
    · have hxP:=hTP e hx
      apply Finset.disjoint_left.mp hPR hxP
      simp only [Finset.mem_insert,Finset.mem_singleton] at hy
      rcases hy with rfl|rfl|rfl|rfl
      · exact (hroots e).1
      · exact (hroots e).2.1
      · exact (hroots e).2.2.1
      · exact (hroots e).2.2.2
    · exact Finset.disjoint_left.mp (hTpr e) hx hy
  obtain ⟨h,RC,RD,hB,hW,hH⟩:=marked_rim_wheel_hubs tail head ktail khead H₀ HK π b (n+1)
    src dst (fun e=>f (src e)) (fun e=>f (dst e)) pr ρ C D hC hD R P T B c
    hroots hcross hrP hPR hPP hsepPR hRR hTP (fun e=>markedRimHubAttachmentRows_card τ first last e)
    hTex hcount hbudget
  refine ⟨h,RC,RD,hB,hW,?_⟩
  intro z
  have hz:=marked_assigned_slot_rows_include τ first last z
  exact ⟨hH _ _ hz.1,hH _ _ hz.2⟩

end Oberwolfach
