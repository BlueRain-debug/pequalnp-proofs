import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Fintype.Pi
import PEqualNP.Defs

-- Adapted from D Lam's L-meta-10852, following Vkuparin, ljste and jfsantoropereira.
namespace PEqualNP.Outside.L_meta_10854_aux

abbrev B := BitVec 256
abbrev Sig := B × B
def top : B := BitVec.allOnes 256
def zero : Sig := (0,0)
def one : Sig := (top,top)
def target : Sig := (top,0)
def neg (a : Sig) : Sig := (~~~a.1,~~~a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1,a.2 ||| b.2) else (a.1 &&& b.1,a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : B :=
  if d then a.1 ^^^ a.2 else a.1 &&& ~~~a.2
def unionSep (d : Bool) : List Sig → B
  | [] => 0
  | a::l => sep d a ||| unionSep d l

def dropped (del v : List Sig) : List Sig := v.filter (fun x => !(del.contains x))

abbrev Cov := B × B × B

def addCov (z : B) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Sig) : Cov :=
  v.foldr (fun a c => addCov (sep d a) c) (0,0,0)

def takeOne (c : Cov) (a : B) : B := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : B) : B :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : B) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : B) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : B) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Sig} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (sep d a)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

private theorem cov_union (d : Bool) (v : List Sig) : (coverage d v).1=unionSep d v := by
  induction v with
  | nil => rfl
  | cons a v ih => change sep d a ||| (coverage d v).1 = (sep d a ||| unionSep d v); rw [ih]

private lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]



def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

def Live : Nat → Nat → Finset Sig → Prop
  | 0, t, S => t = 0 ∧ S = {target}
  | k+1, t, S =>
    (∃ u U a, t = u+1 ∧ S = insert a U ∧ proper a ∧ neg a ∉ insert a U ∧ Live k u (insert (neg a) U)) ∨
    (∃ U a b d, S = insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live k t (insert (bin d a b) U))

lemma Live.stop : Live 0 0 {target} := ⟨rfl,rfl⟩

lemma Live.unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k+1) (t+1) (insert a U) := Or.inl ⟨_,_,_,rfl,rfl,ha,hfresh,tail⟩

lemma Live.binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k+1) t (insert a (insert b U)) := Or.inr ⟨_,_,_,_,rfl,ha,hb,hab,hfresh,tail⟩

lemma liveInd {P : ∀ k t S, Live k t S → Prop}
    (stop : P 0 0 {target} Live.stop)
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)), P k t (insert (neg a) U) tail → P (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)), P k t (insert (bin d a b) U) tail → P (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t S} (h : Live k t S) : P k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl⟩ := h
    exact stop
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)

lemma liveCases {P : ∀ k t S, Live k t S → Prop}
    (stop : P 0 0 {target} Live.stop)
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)), P (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)), P (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t S} (h : Live k t S) : P k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl⟩ := h
    exact stop
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail
    · exact binary ha hb hab hf tail

private lemma target_proper : proper target := by unfold proper target zero one top; decide
private lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h using liveInd with
  | stop => simpa using target_proper
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using liveInd with
  | stop => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

private lemma sep_unary (t : Nat) (a : Sig) (i : Nat)
    (h : (sep (decide (0<t)) (neg a)).getLsbD i = true) :
    (sep true a).getLsbD i = true := by
  by_cases hi : i < 256
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 256 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 256
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 256 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 256)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 256) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h using liveInd with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 256 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 256)] <;> simp [hi]
  | unary ha hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ,decide_true]
    rcases hx with rfl | hU
    · exact ⟨_,Finset.mem_insert_self _ _,sep_unary _ _ _ h⟩
    · exact ⟨x,Finset.mem_insert_of_mem hU,sep_weaken _ _ _ hi h⟩
  | binary ha hb hab hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases sep_binary _ _ _ _ _ h with h | h
      · exact ⟨_,Finset.mem_insert_self _ _,h⟩
      · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),h⟩
private lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).getLsbD i = true ↔ ∃ a ∈ v, (sep d a).getLsbD i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih => simp only [unionSep,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp] <;> aesop

private lemma live_cover {k t S} {v : List Sig} (h : Live k t S) (he : v.toFinset=S) :
    unionSep (decide (0<t)) v = top := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨a,hm,ha⟩ := live_sep h i hi
  have hmem : a ∈ v := List.mem_toFinset.mp (he.symm ▸ hm)
  simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using (mem_unionSep _ _ _).2 ⟨a,hmem,ha⟩

private lemma union_append (d : Bool) (l r : List Sig) :
    unionSep d (l++r) = unionSep d l ||| unionSep d r := by
  induction l with
  | nil => simp [unionSep]
  | cons a l ih => simp [unionSep,ih,BitVec.or_assoc]

def keepOf (U : Finset Sig) (del : List Sig) : List Sig := del.filter (fun a => decide (a ∈ U))

private lemma edit_list {v del : List Sig} {U : Finset Sig}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset = del.toFinset ∪ U) :
    (keepOf U del ++ dropped del v).Nodup ∧ (keepOf U del ++ dropped del v).toFinset = U := by
  have memv (x : Sig) : x ∈ v ↔ x ∈ del ∨ x ∈ U := by
    change x ∈ v ↔ _
    rw [← List.mem_toFinset,he]
    simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _,hv.filter _,?_⟩
    intro a ha b hb eq
    subst b
    simp [keepOf] at ha
    simp [dropped] at hb
    exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset,List.mem_append,List.mem_filter,keepOf,dropped,decide_eq_true_eq,
      Bool.not_eq_true',List.contains_eq_mem,memv]
    by_cases h : x ∈ del <;> simp_all

private lemma recover_perm (del v : List Sig) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del, x ∈ v) : v.Perm (del ++ dropped del v) := by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd,hv.filter _,?_⟩
    intro a ha b hb e
    subst b
    simp [dropped] at hb
    exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset,List.mem_append,dropped,List.mem_filter,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all

private lemma one_rest (d : Bool) {v : List Sig} {a : Sig} (hv : v.Nodup) (ha : a ∈ v) :
    v.length-1=(dropped [a] v).length ∧
      takeOne (coverage d v) (sep d a)=unionSep d (dropped [a] v) := by
  have p := recover_perm [a] v hv (by simp) (by simpa using ha)
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_one _ _).trans (cov_union _ _)

private lemma two_rest (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    v.length-2=(dropped [a,b] v).length ∧
      takeTwo (coverage d v) (sep d a) (sep d b)=unionSep d (dropped [a,b] v) := by
  have p := recover_perm [a,b] v hv (by simp [hab]) (by simp [ha,hb])
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_two _ _ _).trans (cov_union _ _)

open PEqualNP.CircuitLowerBounds

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  obtain ⟨p,n⟩ := a
  simp only [bin,one,zero,top,reduceCtorEq,ite_true,ite_false,BitVec.and_allOnes,BitVec.or_allOnes,BitVec.and_zero,BitVec.or_zero,BitVec.and_self,BitVec.or_self,Prod.mk.injEq,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one,top]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def isNot (op : GateOp) : Bool := match op with | .not => true | _ => false

lemma isNot_iff (op : GateOp) : isNot op = true ↔ op = .not := by cases op <;> simp [isNot]

def witness (allow : Bool) (w : List Sig) (z : Sig) : Prop :=
  (allow = true ∧ ∃ a ∈ w, proper a ∧ z = neg a) ∨
  (allow = false ∧ ∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness false w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨rfl,d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness (isNot g.op) w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness true w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨rfl,a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness false w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness false w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

private lemma pull_gate {flag : Bool} {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness flag w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' + t + flag.toNat ≤ k+1+t' ∧ t' ≤ t+flag.toNat ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by cases flag <;> simp <;> omega,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨flagOn,a,ha,hp',eq⟩ | ⟨flagOff,d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,by simp [flagOn] <;> omega,by simp [flagOn],Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,by simp [flagOff] <;> omega,by omega,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by cases flag <;> simp <;> omega,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k + gs.countP (fun g => isNot g.op) ≤ gs.length + t ∧ t ≤ gs.countP (fun g => isNot g.op) ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,by simp,Live.stop,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,hcount,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hcnt,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    refine ⟨l,u,T,?_,?_,hu,hT⟩ <;>
      cases hf : isNot g.op <;> simp [List.countP_cons,hf] at hl hcnt ⊢ <;> omega

def bit (side : Bool) (i : Fin 256) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 256).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
private lemma bit_neg (s i) (a : Sig) : bit s i (neg a) = !(bit s i a) := by
  cases s <;> simp only [bit,neg,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and]
private lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp only [bit,bin,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]

private lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl

private lemma run_bit (s i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _ _
    | cons a l ih =>
      change bit s i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _ _
    | cons a l ih =>
      change bit s i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit s i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _ _

private lemma execute_bits (gs : List Gate) (s i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit s i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit s i g w (hg g (by simp))]


def evalT (T : ℕ) (x : Fin 7 → Bool) := Nat.testBit T (∑ i : Fin 7, if x i then 2 ^ (i : ℕ) else 0)
def sample (raw : List Sig) (s : Bool) (i : Fin 256) (j : Fin 7) := bit s i (raw.getD j.val zero)
private lemma sample_list (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 7 => raw.getD j.val zero) = raw) (s i) : List.ofFn (sample raw s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 7 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (T : ℕ) (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 7 => raw.getD j.val zero) = raw)
    (sample_ok : ∀ s i, evalT T (sample raw s i) = s) (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = evalT T x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample raw s i)
    rw [sample_list raw raw_id,sample_ok] at eq
    exact eq
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project true ⟨i,hi⟩
      change (w.getD C.output zero).1.getLsbD i = true at p
      change _ = (BitVec.allOnes _).getLsbD _
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using p
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project false ⟨i,hi⟩
      change (w.getD C.output zero).2.getLsbD i = false at p
      have hz : (0 : B).getLsbD i=false := by simp
      exact p.trans hz.symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

private lemma necessary (raw : List Sig) (every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true) {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset=S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_,hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,h⟩ := live_sep l i hi
    have ba : b ≠ a := fun he => hn (he ▸ hb)
    have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
    have eq := (mem_unionSep true _ _).mpr ⟨b,hm,sep_weaken _ _ _ hi h⟩
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using eq
  simp [cov] at fail

def special : List Sig := []
def gateAvailable (v : List Sig) (g : Sig) : Bool :=
  !(v.contains g) && g != zero && g != one

def tryGate (k t : Nat) (r : List Sig → Bool) (v rest : List Sig) (n : Nat) (c : B) (g : Sig)
    (keep : List (List Sig)) : Bool :=
  let d := decide (0<t)
  let base := sep d g ||| c
  if n = k-t then
    base == top && gateAvailable v g && r (g::rest)
  else keep.any (fun h => decide (n+h.length+1 ≤ k-t+1) &&
    (base ||| unionSep d h == top) && gateAvailable v g && r (g::(h++rest)))

def unaryAt (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a : Sig) : Bool :=
  !(special.contains a) &&
    tryGate k t r v (dropped [a] v) (v.length-1) (takeOne c (sep (decide (0<t)) a)) (neg a) [[],[a]]

def unaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  let c := coverage (decide (0<t)) v
  v.any (unaryAt k t r v c)

def allowedKeeps (a b : Sig) : List (List Sig) :=
  [[],[a],[b],[a,b]].filter (fun w => w.all fun x => !(special.contains x))

def fastBinary (r : List Sig → Bool) (v : List Sig) (a b : Sig) (ua ub : B) : Bool :=
  let rest := dropped [a,b] v
  let use := fun (g : Sig) => gateAvailable v g && r (g::rest)
  ((ua &&& ~~~b.1) == 0 && (ub &&& ~~~a.1) == 0 &&
    !(special.contains a) && !(special.contains b) && use (bin false a b)) ||
    ((ua &&& b.2) == 0 && (ub &&& a.2) == 0 && use (bin true a b))

def slowBinary (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a b : Sig) : Bool :=
  let rest := dropped [a,b] v
  let mask := takeTwo c (sep (decide (0<t)) a) (sep (decide (0<t)) b)
  ((!(special.contains a) && !(special.contains b)) &&
    tryGate k t r v rest (v.length-2) mask (bin false a b) [[],[a],[b],[a,b]]) ||
    tryGate k t r v rest (v.length-2) mask (bin true a b) (allowedKeeps a b)

def scanPairs {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => false
  | a :: t => t.any (p a) || scanPairs p t

lemma scanPairs_complete {α : Type} (p : α → α → Bool) {a b : α} {v : List α}
    (ha : a ∈ v) (hb : b ∈ v) (hne : a ≠ b)
    (hab : p a b = true) (hba : p b a = true) : scanPairs p v = true := by
  induction v with
  | nil => simp at ha
  | cons h v ih =>
    simp only [scanPairs, Bool.or_eq_true]
    by_cases eqA : a = h
    · subst h
      exact Or.inl (List.any_eq_true.mpr ⟨b, (List.mem_cons.mp hb).resolve_left (Ne.symm hne), hab⟩)
    · have ha' := (List.mem_cons.mp ha).resolve_left eqA
      by_cases eqB : b = h
      · subst h
        exact Or.inl (List.any_eq_true.mpr ⟨a, ha', hba⟩)
      · exact Or.inr (ih ha' ((List.mem_cons.mp hb).resolve_left eqB))

def binaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  let d := decide (0<t)
  let c := coverage d v
  if t == 0 && v.length == k+2 then
    let acts := v.map (fun a => (a, c.2.1 &&& sep false a))
    scanPairs (fun a b => fastBinary r v a.1 b.1 a.2 b.2) acts
  else scanPairs (slowBinary k t r v c) v

def stepTest (k t : Nat) (v : List Sig) (u b : List Sig → Bool) : Bool :=
  if t>k+1 ∨ v.length>k+1-t+1 then false else
    v == [target] || (decide (0<t) && unaryMoves k (t-1) u v) || binaryMoves k t b v

def search : Nat → Nat → List Sig → Bool
  | 0, _, v => v == [target]
  | k+1,t,v => stepTest k t v (search k (t-1)) (search k t)

private lemma gate_found {k t m : Nat} {v rest h : List Sig} {g : Sig} {opts : List (List Sig)}
    {S : Finset Sig} {r : List Sig → Bool} (l : Live m t S)
    (hle : m ≤ k) (hp : proper g) (ha : g ∉ v) (hh : h ∈ opts)
    (hn : (g::(h++rest)).Nodup) (he : (g::(h++rest)).toFinset=S)
    (hr : r (g::(h++rest)) = true) : tryGate k t r v rest rest.length (unionSep (decide (0<t)) rest) g opts = true := by
  obtain ⟨ht,hc⟩ := live_size l
  rw [←he,List.toFinset_card_of_nodup hn] at hc
  simp only [List.length_cons,List.length_append] at hc
  have hl : rest.length+h.length+1 ≤ k-t+1 := by omega
  have cv := live_cover l he
  rw [unionSep,union_append] at cv
  have cov : (sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest) ||| unionSep (decide (0<t)) h = top := by
    rw [← cv]; ac_rfl
  by_cases tight : rest.length=k-t
  · have hz : h.length=0 := by omega
    have hem : h=[] := List.length_eq_zero_iff.mp hz
    subst h
    have ok : sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest = top := by
      simpa [unionSep] using cov
    simp [tryGate,tight,ok,gateAvailable,ha,hp.1,hp.2,hr] at *
  · have hav : gateAvailable v g = true := by simp [gateAvailable, ha, hp.1, hp.2]
    simp only [tryGate, ite_eq_right tight, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq, hav, and_true]
    exact ⟨h,hh,⟨hl,cov⟩,hr⟩

private lemma unique_needed (c : Cov) (a b : Sig) (op : Bool)
    (h : sep false (bin op a b) ||| takeTwo c (sep false a) (sep false b)=top) :
    ((c.2.1 &&& sep false a) &&& (if op then b.2 else ~~~b.1)) |||
    ((c.2.1 &&& sep false b) &&& (if op then a.2 else ~~~a.1))=0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hh := congrArg (fun z : B => z.getLsbD i) h
  clear h
  cases op <;> simp only [sep,bin,ite_false,ite_true,takeTwo,top,BitVec.getLsbD_allOnes,
    BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,BitVec.getLsbD_zero,
    reduceCtorEq,hi,decide_true,Bool.true_and] at hh ⊢ <;>
    cases ax : a.1.getLsbD i <;> cases ay : a.2.getLsbD i <;>
    cases bx : b.1.getLsbD i <;> cases byy : b.2.getLsbD i <;>
    cases um : c.2.1.getLsbD i <;> simp [ax,ay,bx,byy,um] at hh ⊢

private lemma fast_ok {k r v c a b}
    (hlen : v.length-2=k) (h : slowBinary k 0 r v c a b = true) :
    fastBinary r v a b (c.2.1 &&& sep false a) (c.2.1 &&& sep false b) = true := by
  simp only [slowBinary,tryGate,Nat.sub_zero,hlen,ite_true,decide_false,Bool.or_eq_true,
    Bool.and_eq_true,beq_iff_eq] at h
  simp only [fastBinary, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  rcases h with ⟨⟨ha,hb⟩,⟨hc,hav⟩,hr⟩ | ⟨⟨hc,hav⟩,hr⟩
  · obtain ⟨h1,h2⟩ := BitVec.or_eq_zero_iff.mp (unique_needed c a b false hc)
    exact Or.inl ⟨⟨⟨⟨h1,h2⟩,ha⟩,hb⟩,hav,hr⟩
  · obtain ⟨h1,h2⟩ := BitVec.or_eq_zero_iff.mp (unique_needed c a b true hc)
    exact Or.inr ⟨⟨h1,h2⟩,hav,hr⟩

private lemma unary_found {m t k : Nat} {U : Finset Sig} {a : Sig} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a U) (hle : m ≤ k)
    (fresh : neg a ∉ insert a U) (ha : a ∉ special) (l : Live m t (insert (neg a) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (neg a) U → r v = true) :
    unaryMoves k t r v = true := by
  let h := keepOf U [a]
  let rest := dropped [a] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  obtain ⟨hn,eq⟩ := edit_list (del := [a]) (U := U) hv (by simp) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : neg a ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : neg a ∉ U := fun hm => fresh (Finset.mem_insert_of_mem hm)
  have hnd : (neg a::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (neg a::(h++rest)).toFinset=insert (neg a) U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a]] := by by_cases hm : a ∈ U <;> simp [h,keepOf,hm]
  apply List.any_eq_true.mpr
  refine ⟨a,ah,?_⟩
  unfold unaryAt
  obtain ⟨hlen,hmask⟩ := one_rest (decide (0<t)) hv ah
  rw [hlen,hmask]
  apply Bool.and_eq_true_iff.mpr
  exact ⟨by simp [ha], gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩

private lemma slow_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ special → d = true ∧ a ∉ U)
    (hrb : b ∈ special → d = true ∧ b ∉ U)
    (l : Live m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    slowBinary k t r v (coverage (decide (0<t)) v) a b = true := by
  let g := bin d a b
  let h := keepOf U [a,b]
  let rest := dropped [a,b] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  obtain ⟨hn,eq⟩ := edit_list (del := [a,b]) (U := U) hv (by simp [hab]) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : g ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : g ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hnd : (g::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (g::(h++rest)).toFinset=insert g U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a],[b],[a,b]] := by
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp [h,keepOf,ha,hb]
  have allow : h ∈ allowedKeeps a b := by
    apply List.mem_filter.mpr
    refine ⟨opts,List.all_eq_true.mpr (fun x hx => ?_)⟩
    have hm : x ∈ U := (List.mem_filter.mp hx).2 |> of_decide_eq_true
    rcases List.mem_cons.mp (List.mem_filter.mp hx).1 with rfl | hx
    · simpa using fun ha : x ∈ special => (hra ha).2 hm
    · obtain rfl := List.mem_singleton.mp hx
      simpa using fun hb : x ∈ special => (hrb hb).2 hm
  obtain ⟨hlen,hmask⟩ := two_rest (decide (0<t)) hv ah bh hab
  unfold slowBinary
  dsimp only
  rw [hlen,hmask]
  cases d with
  | false =>
    have na : a ∉ special := fun ha => Bool.false_ne_true (hra ha).1
    have nb : b ∉ special := fun hb => Bool.false_ne_true (hrb hb).1
    apply Bool.or_eq_true_iff.mpr
    left
    exact Bool.and_eq_true_iff.mpr ⟨by simp [na,nb],
      gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩
  | true =>
    apply Bool.or_eq_true_iff.mpr
    right
    exact gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn allow hnd e (ih _ hnd e)

private lemma binary_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ special → d = true ∧ a ∉ U)
    (hrb : b ∈ special → d = true ∧ b ∉ U)
    (l : Live m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    binaryMoves k t r v = true := by
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have h1 := slow_found hv he hle hab fresh hra hrb l ih
  have e' : v.toFinset = insert b (insert a U) := by rwa [Finset.insert_comm b a]
  have hf : bin d b a ∉ insert b (insert a U) := by rwa [bin_comm d b a, Finset.insert_comm b a]
  have ht : Live m t (insert (bin d b a) U) := by rwa [bin_comm d b a]
  have h2 := slow_found hv e' hle hab.symm hf hrb hra ht (by simpa only [bin_comm d b a] using ih)
  unfold binaryMoves
  split
  · rename_i cut
    simp only [Bool.and_eq_true, beq_iff_eq] at cut
    obtain ⟨rfl,hvlen⟩ := cut
    have hlen : v.length - 2 = k := by omega
    let f := fun x => (x, (coverage false v).2.1 &&& sep false x)
    have na : f a ∈ v.map f := List.mem_map_of_mem ah
    have nb : f b ∈ v.map f := List.mem_map_of_mem bh
    exact scanPairs_complete _ na nb (fun e => hab (congrArg Prod.fst e))
      (fast_ok hlen h1) (fast_ok hlen h2)
  · exact scanPairs_complete _ ah bh hab h1 h2

lemma reduced_step {m t S : Nat} {s : Finset Sig} {v : List Sig} {u b : List Sig → Bool}
    (h : Live m t s) (hb : m ≤ S+1) (hv : v.Nodup) (he : v.toFinset = s)
    (hu : ∀ w, w.Nodup → ∀ l ≤ S, Live l (t-1) w.toFinset → u w = true)
    (hb' : ∀ w, w.Nodup → ∀ l ≤ S, Live l t w.toFinset → b w = true) :
    stepTest S t v u b = true := by
  have size := live_size h
  rw [← he, List.toFinset_card_of_nodup hv] at size
  rw [stepTest, if_neg (by omega)]
  induction h using liveCases with
  | stop =>
    have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [he])
    have eq := List.perm_singleton.mp p
    simp [eq]
  | @unary m t U a ha hf tail =>
    apply Bool.or_eq_true_iff.mpr
    left
    apply Bool.or_eq_true_iff.mpr
    right
    apply Bool.and_eq_true_iff.mpr
    refine ⟨by simp, unary_found hv he (by omega) hf (by simp [special]) tail ?_⟩
    intro w hn hs
    exact hu w hn m (by omega) (hs.symm ▸ tail)
  | @binary m t U a b d ha hc hab hf tail =>
    apply Bool.or_eq_true_iff.mpr
    right
    apply binary_found hv he (by omega) hab hf (by simp [special]) (by simp [special]) tail
    intro w hn hs
    exact hb' w hn m (by omega) (hs.symm ▸ tail)

lemma search_complete {m t : Nat} {S : Finset Sig} (h : Live m t S) (k : Nat) (hk : m ≤ k)
    (v : List Sig) (hv : v.Nodup) (hs : v.toFinset = S) : search k t v = true := by
  induction k generalizing m t S v with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    obtain ⟨rfl,rfl⟩ := h
    have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [hs])
    simp [search, List.perm_singleton.mp p]
  | succ k ih =>
    rw [search]
    apply reduced_step h hk hv hs <;>
      exact fun w hn l hl hh => ih hh hl w hn rfl


lemma notCount (gs : List Gate)
    (single : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j) :
    gs.countP (fun g => isNot g.op) ≤ 1 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have rest : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j := by
      intro i j hi hj
      exact Fin.succ_inj.mp (single i.succ j.succ hi hj)
    by_cases hg : g.op = .not
    · have z : gs.countP (fun h => isNot h.op) = 0 := by
        apply List.countP_eq_zero.mpr
        intro a ha
        obtain ⟨i,hi⟩ := List.mem_iff_get.mp ha
        intro h
        have hiNot : (gs.get i).op = .not := by rw [hi]; exact (isNot_iff _).mp h
        have eqn := single (0 : Fin (g::gs).length) i.succ hg hiNot
        exact Fin.succ_ne_zero i eqn.symm
      have hf : isNot g.op = true := (isNot_iff _).mpr hg
      simp [List.countP_cons,hf,z]
    · have flag : isNot g.op = false := Bool.eq_false_iff.mpr (fun h => hg ((isNot_iff _).mp h))
      simpa [List.countP_cons,flag] using ih rest

def root : List Sig := [
  (0xac08e4ea11114e855409c246026073004020c4a2800280c412cc1106932673ff,0x123d4200092402b80042101484403b003008c81449008412cc0002920252aa),
  (0x42250b056602000a81020c08210504a32617204c22f40100a30f229b1cdb9ccc,0x16e24a4a990800009ac0ca000d04d80840dc0c280c240000a30a0093189318cc),
  (0x11900000806c81200aa411a01882000490c0090015090228c3f0cce3e0e3e0f0,0x94a23445a940d240c100d82241a7d7700b885e88ac6e0028c3a088c3c0e3e0f0),
  (0x204054000101709100102200c258c9080108d4200000cc30fc00f0fc00fc00ff,0x6608201bd04987c06401502a02b27008fcde0334196c830e800f0fc00fc0055),
  (0x4a0b00fa3882084c61408017050402f20c3022d3ea84703f0000ff0000ffff00,0x80040015226409d9410c2424000a2384830032144112e03a0000ff00006ca500),
  (0x8494a00106780600960f55c008203401f0860000146a7fc00000ffffff000000,0x9000090422608840431018da05800842000a0004280ff400000772c25000000),
  (0x11621b14c884b17228f02839f49b885c0b491b1d49117fffffff000000000000,0x2819000000012402203100c91000000230220000020017c51455000000000000)]

def goalTable : Nat := 0xfffffffefffffffcfefefefeeeeeaa00

theorem samples_match : ∀ b i, evalT goalTable (sample root b i) = b := by
  decide +kernel

def Blocked (k t : Nat) (v : List Sig) : Prop :=
  ∀ m ≤ k, ¬ Live m t v.toFinset

def Batch (k t : Nat) : List (List Sig) → Prop
  | [] => True
  | a :: rest => Blocked k t a ∧ Batch k t rest

theorem in_batch {k t ws w} (h : Batch k t ws) (mem : w ∈ ws) : Blocked k t w := by
  induction ws with
  | nil => simp at mem
  | cons a l ih =>
    rcases List.mem_cons.mp mem with rfl | m
    · exact h.1
    · exact ih h.2 m

def sameBank (w v : List Sig) : Bool :=
  w.all v.contains && v.all w.contains

theorem sameBank_eq {w v : List Sig} (h : sameBank w v = true) : w.toFinset = v.toFinset := by
  obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨fun h => List.contains_iff_mem.mp (List.all_eq_true.mp ha a h),
         fun h => List.contains_iff_mem.mp (List.all_eq_true.mp hb a h)⟩

def allowChild (states : List (List Sig)) (w : List Sig) : Bool :=
  !(states.any (sameBank w))

theorem allow_live {k t m states w} (bad : Batch k t states) (sz : m ≤ k)
    (live : Live m t w.toFinset) : allowChild states w = true := by
  have noMatch : states.any (sameBank w) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨v,hv,eq⟩ := List.any_eq_true.mp hh
    exact in_batch bad hv m sz (sameBank_eq eq ▸ live)
  simp [allowChild, noMatch]

theorem block_step {k t v} (unary binary : List (List Sig)) (hu : Batch k (t-1) unary)
    (hb : Batch k t binary) (nd : v.Nodup)
    (ok : stepTest k t v (allowChild unary) (allowChild binary) = false) : Blocked (k+1) t v := by
  intro m small h
  have good := reduced_step (u := allowChild unary) (b := allowChild binary) h small nd rfl
    (fun _ _ _ sz l => allow_live hu sz l) (fun _ _ _ sz l => allow_live hb sz l)
  exact Bool.false_ne_true (ok.symm.trans good)

theorem block_search {k t v} (nd : v.Nodup) (ok : search k t v = false) : Blocked k t v := by
  intro m small live
  exact Bool.false_ne_true (ok.symm.trans (search_complete live k small v nd rfl))

open PEqualNP.CircuitLowerBounds

def edgeFn (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

def replacement : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [7, 8]⟩,
    ⟨.or, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [10, 11]⟩,
    ⟨.and, [1, 4]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [9, 12]⟩,
    ⟨.or, [15, 13]⟩, ⟨.or, [16, 14]⟩], 17⟩

theorem replacement_size : replacement.gates.length = 11 := rfl

theorem replacement_basis : ∀ g ∈ replacement.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [replacement]

set_option maxRecDepth 16000 in
theorem replacement_correct : ∀ x : Fin 7 → Bool, replacement.eval (List.ofFn x) = edgeFn x := by
  decide +kernel

theorem table_agrees : ∀ x : Fin 7 → Bool, edgeFn x = evalT goalTable x := by
  decide +kernel

theorem lower_with_not (gs : List Gate) (o : ℕ)
    (basis : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (oneNot : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (used : ∃ g ∈ gs, g.op = .not)
    (correct : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = edgeFn x)
    (zeroNot : Blocked 9 0 root) (one : Blocked 10 1 root) : 11 ≤ gs.length := by
  by_contra! small
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using basis
  have hout := circuit_target goalTable root rfl samples_match (⟨gs,o⟩ : Circuit) legal
    (fun x => (correct x).trans (table_agrees x))
  obtain ⟨k,t,S,hk,count,live,sub⟩ := extract gs root legal hout
  have eq := necessary root (by decide +kernel) live sub
  have hL : Live k t root.toFinset := eq.symm ▸ live
  have atMostOne := notCount gs oneNot
  have positive : 0 < gs.countP (fun g => isNot g.op) := by
    obtain ⟨g,hg,op⟩ := used
    by_contra! hz
    have absent := List.countP_eq_zero.mp (Nat.le_zero.mp hz) g hg
    exact absent ((isNot_iff _).mpr op)
  by_cases z : t = 0
  · subst t
    exact zeroNot k (by omega) hL
  · have u : t = 1 := by omega
    subst t
    exact one k (by omega) hL



def sig3 : Sig := (0xac08e4ea11114e855409c246026073004020c4a2800280c412cc1106932673ff, 0x123d4200092402b80042101484403b003008c81449008412cc0002920252aa)

def sig4 : Sig := (0x42250b056602000a81020c08210504a32617204c22f40100a30f229b1cdb9ccc, 0x16e24a4a990800009ac0ca000d04d80840dc0c280c240000a30a0093189318cc)

def sig5 : Sig := (0x11900000806c81200aa411a01882000490c0090015090228c3f0cce3e0e3e0f0, 0x94a23445a940d240c100d82241a7d7700b885e88ac6e0028c3a088c3c0e3e0f0)

def sig6 : Sig := (0x204054000101709100102200c258c9080108d4200000cc30fc00f0fc00fc00ff, 0x6608201bd04987c06401502a02b27008fcde0334196c830e800f0fc00fc0055)

def sig7 : Sig := (0x4a0b00fa3882084c61408017050402f20c3022d3ea84703f0000ff0000ffff00, 0x80040015226409d9410c2424000a2384830032144112e03a0000ff00006ca500)

def sig8 : Sig := (0x8494a00106780600960f55c008203401f0860000146a7fc00000ffffff000000, 0x9000090422608840431018da05800842000a0004280ff400000772c25000000)

def sig9 : Sig := (0x11621b14c884b17228f02839f49b885c0b491b1d49117fffffff000000000000, 0x2819000000012402203100c91000000230220000020017c51455000000000000)

def sig10 : Sig := (0x20c0002100210cc, 0x2084200080000980042000404400800100808040000000208000210021088)

def sig11 : Sig := (0xee2defef77134e8fd50bce4e236577a36637e4eea2f681c4b3cf339f9fffffff, 0x16f27f4a99092402bac0ca101d84d83b40fc0ce81c6d0084b3ce00939a935aee)

def sig12 : Sig := (0x2c00002802260f0, 0x23440000000008000400000844030000008880448000002800002800240a0)

def sig13 : Sig := (0xbd98e4ea917dcfa55eadd3e61ae27304d0e0cda2950b82ecd3fcdde7f3e7f3ff, 0x94b23d47a949f642f900da3255a7d77b0bb85ec8bc6f00acd3ec88c3d2e3f2fa)

def sig14 : Sig := (0x200044000101408100000200024041000000c4200000800010001004002400ff, 0x0)

def sig15 : Sig := (0xac48f4ea11117e955419e246c278fb084128d4a28002ccf4feccf1fe93fe73ff, 0x672bf43bd0dbc7ebe405712b4af673b8ffde8fb55dfc8b4faccf0fe92fe52ff)

def sig16 : Sig := (0x80800ea10000804400080060000020000200082800000040000110000267300, 0x0)

def sig17 : Sig := (0xee0be4fa39934ecd7549c257076473f24c30e6f3ea86f0ff12ccff0693ffffff, 0x80163d57226d2ddbf90c6634148e63bf83303adc555be0be12ccff02926ef7aa)

def sig18 : Sig := (0x8400a00000100600140940400020300040000000000200c00000110693000000, 0x0)

def sig19 : Sig := (0xac9ce4eb17794e85d60fd7c60a607701f0a6c4a2946affc412ccffffff2673ff, 0x9123dd2422f2c86bc31439db4dc40bf2030a8c856c9ffc412cc772eb70252aa)

def sig20 : Sig := (0xc412cc000000000000, 0x10000000012402200000001000000200200000000000841044000000000000)

def sig21 : Sig := (0xbd6afffed995fff77cf9ea7ff6fbfb5c4b69dfbfc913ffffffff1106932673ff, 0x281b3d4200092402b83142d91484403b303208c8164917c516dd0002920252aa)

def sig22 : Sig := (0x8300008300c380c0, 0x14a20040890000008000c8000104d00000880c080c24000083000083008300c0)

def sig23 : Sig := (0x53b50b05e66e812a8ba61da8398704a7b6d7294c37fd0328e3ffeefbfcfbfcfc, 0x96e27e4fb948d240dbc0da224da7df784bdc5ea8ac6e0028e3aa88d3d8f3f8fc)

def sig24 : Sig := (0x2cc0002902270fc, 0x23c42000800009800420004844038001008880448000002880002900250a8)

def sig25 : Sig := (0xffbdefeff77fcfafdfafdfee3be777a7f6f7edeeb7ff83ecf3ffffffffffffff, 0x96f27f4fb949f642fbc0da325da7df7b4bfc5ee8bc6f00acf3ee88d3daf3fafe)

def sig26 : Sig := (0xa000209800d800cc, 0x660020099000000024000000000000000cc002000040000a000009000900044)

def sig27 : Sig := (0x62655f056703709b81122e08e35dcdab271ff46c22f4cd30ff0ff2ff1cff9cff, 0x16e2ca4bbd0c987c9ec0df02ad2fff08cfddec3b4db6c830eb0af0ff18ff18dd)

def sig28 : Sig := (0x420100002002000801000000010400a204102040228400000000220000db9c00, 0x0)

def sig29 : Sig := (0x4a2f0bff7e82084ee1428c1f250506f32e3722dfeaf4713fa30fff9b1cffffcc, 0x96e64a5fbb6c09d9dbccee240d0efb8cc3dc3e3c4d36e03aa30aff9318ffbdcc)

def sig30 : Sig := (0x4000106000000800204000000040120060000006001000000229b1c000000, 0x0)

def sig31 : Sig := (0xc6b5ab05667a060a970f5dc8292534a3f697204c36fe7fc0a30fffffffdb9ccc, 0x1fe24adadb2e08849ef1cb8dad5cd88c60dcac284ea4ff40a30a77bf3d9318cc)

def sig32 : Sig := (0x200b044000000200000808200100000201000c00100100a30f000000000000, 0x0)

def sig33 : Sig := (0x53671b15ee86b17aa9f22c39f59f8cff2f5f3b5d6bf57fffffff229b1cdb9ccc, 0x3efb4a4a99092402baf1cac91d04d80a70fe0c280e2417c5b75f0093189318cc)

def sig34 : Sig := (0x40300000f00000fc0000, 0x12004085800000400000a2300830020104112c0300000f000006c0000)

def sig35 : Sig := (0x6a4b54fa398378dd6150a217c75ccbfa0d38f6f3ea84fc3ffc00fffc00ffffff, 0x86648215bf6499fd474c3526a02b27848fcdf2374196e83ae800fffc00fca555)

def sig36 : Sig := (0x4c000000f0fc00000000, 0x4080404000100a00800000000a0004080c8000000702c00000000)

def sig37 : Sig := (0xa4d4f40107797691961f77c0ca78fd09f18ed420146afff0fc00fffffffc00ff, 0xf608291ff2698fc0671158fa07b2784afcde0334396ff70e800f7fc25fc0055)

def sig38 : Sig := (0x4010000000301000102000c01888080108100000004c30fc00000000000000, 0x0)

def sig39 : Sig := (0x31625f14c985f1f328f02a39f6dbc95c0b49df3d4911fffffffff0fc00fc00ff, 0x2e798201bd05bc7e267115cbb02b2702bfefe0334396dff5fc55f0fc00fc0055)

def sig40 : Sig := (0xcc, 0x0)

def sig42 : Sig := (0x20e000e0f800f800fc, 0x6600201b900904002401002002307000bcc402000060020e00080d000f00054)

def sig43 : Sig := (0x73f55f05e76ff1bb8bb63fa8fbdfcdafb7dffd6c37fdcf38fffffefffcfffcff, 0x96e2fe4fbd4cda7cdfc0df22edafff78cfddfebbedfec838ebaaf8ffd8fff8fd)

def sig44 : Sig := (0x70000000ff0000000000, 0x10022408800000000400080084000020004000e0000000770000000000)

def sig45 : Sig := (0xce9fa0fb3efa0e4cf74fd5d70d2436f3fcb622d3feee7fff0000ffffffffff00, 0x89040095626609dd453d25ada05a2384a300b2144392ff7a0000ff2c256ca500)

def sig46 : Sig := (0x20010088000402040001104000050080002114800703f0000000000000000, 0x0)

def sig47 : Sig := (0x5b6b1bfef886b97e69f0a83ff59f8afe0f793bdfeb957fffffffff0000ffff00, 0xa81d001522652ddb613d24ed100a2386b32232144312f7ff1455ff00006ca500)

def sig48 : Sig := (0x21000, 0x0)

def sig50 : Sig := (0x420100002002000801000000010400a204102040228400280000ee0000fbfc00, 0x800000052040004041000020000203000300120000020028000088000060a000)

def sig51 : Sig := (0x5bbf0bfffeee896eebe69dbf3d8706f7bef72bdffffd733fe3fffffbfcfffffc, 0x96e67e5fbb6cdbd9dbccfe264daffffccbdc7ebced7ee03ae3aaffd3d8fffdfc)

def sig52 : Sig := (0x7fc00000000000000000, 0x800000000000000003100890000000020000000020017400000000000000000)

def sig53 : Sig := (0x95f6bb15cefcb772beff7df9fcbbbc5dfbcf1b1d5d7b7fffffffffffff000000, 0x2919009042272c86243101cdb05800863022a0004280ffc51455772c25000000)

def sig54 : Sig := (0x210000000, 0x0)

def sig56 : Sig := (0x940001066800008206158008000401b0860000146803000000eefbfc000000, 0x0)

def sig57 : Sig := (0xd7b5ab05e67e872a9faf5de839a734a7f6d7294c37ff7fe8e3fffffffffbfcfc, 0x9fe27edffb6edac4dff1dbafedffdffc6bdcfea8eeeeff68e3aafffffdf3f8fc)

def sig60 : Sig := (0x11200b04c004812208a00828308300040241090c01110328e3ff000000000000, 0x0)

def sig61 : Sig := (0x53f71b15eeeeb17aabf63db9fd9f8cffbfdf3b5d7ffd7fffffffeefbfcfbfcfc, 0xbefb7e4fb949f642fbf1daeb5da7df7a7bfe5ea8ae6e17edf7ff88d3d8f3f8fc)

def sig62 : Sig := (0x20c000c0e000e000f0, 0x4200001a900904000001002002307000b88400000060020c00080c000e00050)

def sig63 : Sig := (0x31d05400816df1b10ab433a0dadac90c91c8dd201509ce38fff0fcffe0ffe0ff, 0x96e2b645bd44da7cc740dd22e1aff7708fcdfebbedfec838eba0f8ffc0ffe0f5)

def sig64 : Sig := (0x280000cc0000e3e000, 0x800000052040004041000020000203000300120000020028000088000060a000)

def sig65 : Sig := (0x5b9b00fab8ee896c6be491b71d8602f69cf02bd3ff8d723fc3f0ffe3e0fffff0, 0x94a63455ab64dbd9c10cfc2641aff7f48b887e9ced7ee03ac3a0ffc3c0efe5f0)

def sig66 : Sig := (0x90000000680000020411800800000090800000140802000000cce3e0000000, 0x0)

def sig67 : Sig := (0x9594a001867c87209eaf55e018a23405f0c60900156b7fe8c3f0ffffffe3e0f0, 0x9da234d5eb66dac4c531d9afe1ffd7f42b88fe88eeeeff68c3a0ffefe5e3e0f0)

def sig68 : Sig := (0x110000008004812008a00020108200040040090001010228c3f0000000000000, 0x0)

def sig69 : Sig := (0x11f21b14c8ecb1722af439b9fc9b885c9bc91b1d5d197fffffffcce3e0e3e0f0, 0xbcbb3445a941f642e131d8eb51a7d7723baa5e88ae6e17edd7f588c3c0e3e0f0)

def sig81 : Sig := (0x280844ea1101488540008206024043000020c4a28000800410001104002673ff, 0x0)

def sig82 : Sig := (0xee4bf4fa39937edd7559e257c77cfbfa4d38f6f3ea86fcfffeccfffe93ffffff, 0x8676bf57bf6dbdffff4c7736b4af67bf8ffdfaff55dfe8befaccfffe92fef7ff)

def sig83 : Sig := (0x420100002002000801000000010400a20410204022840000a000229800db9ccc, 0x660020099000000024000000000000000cc002000040000a000009000900044)

def sig84 : Sig := (0x6a6f5fff7f8378dfe152ae1fe75dcffb2f3ff6ffeaf4fd3fff0fffff1cffffff, 0x96e6ca5fbf6c99fddfccff26ad2fff8ccfddfe3f4db6e83aeb0affff18ffbddd)

def sig87 : Sig := (0x7c000000fffc00000000, 0x100224088404000104a00800840000a0004080e8000000772c00000000)

def sig88 : Sig := (0xeedff4fb3ffb7eddf75ff7d7cf7cfffbfdbef6f3feeefffffc00ffffffffffff, 0x8f648295ff6699fd477d35afa07b2784afcdf2374396ff7ae800fffc25fca555)

def sig91 : Sig := (0x4210100880305020502011c41888580908121148007c3ffc00000000000000, 0x0)

def sig92 : Sig := (0x7b6b5ffef987f9ff69f0aa3ff7dfcbfe0f79ffffeb95fffffffffffc00ffffff, 0xae7d8215bf65bdff677d35efb02b2786bfeff2374396fffffc55fffc00fca555)

def sig99 : Sig := (0x28c000cce000e3e0f0, 0x84200005a940904041001022002307000b88520000060028c00088c000e0a050)

def sig100 : Sig := (0x7bdb54fab9eff9fd6bf4b3b7dfdecbfe9df8fff3ff8dfe3ffff0ffffe0ffffff, 0x96e6b655bf64dbfdc74cfd26e1aff7f48fcdfebfedfee83aeba0ffffc0ffe5f5)

def sig220 : Sig := (0x100000240000, 0x0)

def sig221 : Sig := (0x6a0b44fa398348cd61408217074443f20c30e6f3ea84f03f1000ff0400ffffff, 0x80040015226409d9410c2424000a2384830032144112e03a0000ff00006ca500)

def sig235 : Sig := (0x100400000000, 0x0)

def sig236 : Sig := (0xa494e40107794681960f57c00a607501f086c420146affc01000ffffff2400ff, 0x9000090422608840431018da05800842000a0004280ff400000772c25000000)

def sig244 : Sig := (0x1000000000000000, 0x0)

def sig245 : Sig := (0x31625f14c985f1f328f02a39f6dbc95c0b49df3d4911ffffffff1004002400ff, 0x2819000000012402203100c91000000230220000020017c51455000000000000)

def sig255 : Sig := (0x2000f0, 0x0)

def sig256 : Sig := (0x31904400816dc1a10aa413a01ac2410490c0cd2015098228d3f0dce7e0e7e0ff, 0x94a23445a940d240c100d82241a7d7700b885e88ac6e0028c3a088c3c0e3e0f0)

def sig264 : Sig := (0x62254f056703408b81020e08234545a32617e46c22f48100b30f329f1cff9cff, 0x16e24a4a990800009ac0ca000d04d80840dc0c280c240000a30a0093189318cc)

def sig280 : Sig := (0xee09e4ea31134e8d5509c246036473a24430e4e2a28680c412cc330693ffffff, 0x123d4200092402b80042101484403b003008c81449008412cc0002920252aa)

def sig423 : Sig := (0xc625ab056612060a950b4c48212534a36617204c22f601c0a30f339f9fdb9ccc, 0x16e24a4a990800009ac0ca000d04d80840dc0c280c240000a30a0093189318cc)

def sig432 : Sig := (0x8300000000000000, 0x0)

def sig440 : Sig := (0xa000000000000000, 0x0)

def sig568 : Sig := (0x280000000, 0x0)

def sig570 : Sig := (0x2c0000000000000, 0x0)

def sig689 : Sig := (0xac98e4ea11794e85560dd3c60a607300d0a0c4a2940a82c412ccdde7f32673ff, 0x123d4200092402b80042101484403b003008c81449008412cc0002920252aa)

def sig698 : Sig := (0xbd08e4ea9115cfa55ca9c26612e273044060cda2810382ecd3fc1106932673ff, 0x123d4200092402b80042101484403b003008c81449008412cc0002920252aa)

def sig738 : Sig := (0x9590a000807c87201ead51e018a23004d0c00900150b02e8c3f0dde7f3e3e0f0, 0x94a23445a940d240c100d82241a7d7700b885e88ac6e0028c3a088c3c0e3e0f0)

def sig745 : Sig := (0x53250b05e606812a89a20c28318704a72657294c23f50328e3ff229b1cdb9ccc, 0x16e24a4a990800009ac0ca000d04d80840dc0c280c240000a30a0093189318cc)

def sig753 : Sig := (0x20c000000000000000, 0x0)

def sig754 : Sig := (0x314054008105f1b108b02220d2dac90c0148dd200101ce38fff0f0fc00fc00ff, 0x6608201bd04987c06401502a02b27008fcde0334196c830e800f0fc00fc0055)

def sig761 : Sig := (0x280000000000000000, 0x0)

def sig762 : Sig := (0x5b0b00fab886896c69e08037158602f60c702bd3eb85723fc3f0ff0000ffff00, 0x80040015226409d9410c2424000a2384830032144112e03a0000ff00006ca500)

def sig768 : Sig := (0x2000000000000000000, 0x0)

def sig769 : Sig := (0x9594a001867c87209eaf55e018a23405f0c60900156b7fe8c3f0ffffff000000, 0x9000090422608840431018da05800842000a0004280ff400000772c25000000)

def sig875 : Sig := (0xac48f4ea11117e955419e246c278fb084128d4a28002ccf4fecc1106932673ff, 0x123d4200092402b80042101484403b003008c81449008412cc0002920252aa)

def sig876 : Sig := (0x42651b056602301a81122c08e11d8cab271f304c22f44d30ff0f229b1cdb9ccc, 0x16e24a4a990800009ac0ca000d04d80840dc0c280c240000a30a0093189318cc)

def sig888 : Sig := (0x11d01000806cb1300ab431a0d89a880c91c8190015094e38fff0cce3e0e3e0f0, 0x94a23445a940d240c100d82241a7d7700b885e88ac6e0028c3a088c3c0e3e0f0)

def sig900 : Sig := (0x4c000000000000000000, 0x0)

def sig901 : Sig := (0x84d4b00106783610961f75c0c838bc09f18e1000146a7ff0fc00ffffff000000, 0x9000090422608840431018da05800842000a0004280ff400000772c25000000)

def sig904 : Sig := (0x40300000000000000000, 0x0)

def sig905 : Sig := (0x4a4b10fa3882385c6150a017c51c8afa0d3832d3ea847c3ffc00ff0000ffff00, 0x80040015226409d9410c2424000a2384830032144112e03a0000ff00006ca500)

def sig1017 : Sig := (0xa440f4000111769114196240c278f9084108d4200002ccf0fc00f1fe93fc00ff, 0x6608201bd04987c06401502a02b27008fcde0334196c830e800f0fc00fc0055)

def sig1065 : Sig := (0x110000000000, 0x0)

def sig1189 : Sig := (0xce0ba0fa38920e4c7549c057052432f24c3022d3ea8670ff0000ff0693ffff00, 0x80040015226409d9410c2424000a2384830032144112e03a0000ff00006ca500)

def sig1221 : Sig := (0x9562bb14c894b7723cf96879f4bbb85c4b491b1d49137fffffff110693000000, 0x2819000000012402203100c91000000230220000020017c51455000000000000)

def sig1228 : Sig := (0xc00000000000000000, 0x0)

def sig1447 : Sig := (0xc38000, 0x0)

def sig1449 : Sig := (0x8300000000, 0x0)

def sig1549 : Sig := (0x200000d80000, 0x0)

def sig1555 : Sig := (0x220000000000, 0x0)

def sig1556 : Sig := (0xc695a001267a0608970f55c0092434a3f496204036ee7fc00000ffffffdb9c00, 0x9000090422608840431018da05800842000a0004280ff400000772c25000000)

def sig1560 : Sig := (0x53631b14e886b17a29f02839f59f88fe0f593b5d6b957fffffff220000db9c00, 0x2819000000012402203100c91000000230220000020017c51455000000000000)

def sig1565 : Sig := (0x624154002103709901102200c35cc9aa0518f4602284cc30fc00f2fc00ff9cff, 0x6608201bd04987c06401502a02b27008fcde0334196c830e800f0fc00fc0055)

def sig1594 : Sig := (0x42b50b05666a000a83061d88290504a3b697204c36fc0300a30feefbfcdb9ccc, 0x16e24a4a990800009ac0ca000d04d80840dc0c280c240000a30a0093189318cc)

def sig1848 : Sig := (0x53910000a06e81280ba411a0198600a694d02940378d0228c3f0eee3e0fbfcf0, 0x94a23445a940d240c100d82241a7d7700b885e88ac6e0028c3a088c3c0e3e0f0)

def sig1853 : Sig := (0xc0e000000000, 0x0)

def sig1868 : Sig := (0xcc0000000000, 0x0)

def sig1882 : Sig := (0x20d054000169709102143380ca58c9089188d4201408ce30fc00fcffe0fc00ff, 0x6608201bd04987c06401502a02b27008fcde0334196c830e800f0fc00fc0055)

def sig1888 : Sig := (0x4a9b00fa38ea084c634491970d0402f29cb022d3fe8c723f0000ffe3e0ffff00, 0x80040015226409d9410c2424000a2384830032144112e03a0000ff00006ca500)

def sig1893 : Sig := (0x11f21b14c8ecb1722af439b9fc9b885c9bc91b1d5d197fffffffcce3e0000000, 0x2819000000012402203100c91000000230220000020017c51455000000000000)

def sig3115 : Sig := (0x53f71b15eeeeb17aabf63db9fd9f8cffbfdf3b5d7ffd7f3bed33eef96cd98c00, 0xffedc2bdfff6dbfd47ffbdefeb7bbfc4ffcff737ebb6ff7bed33fffd6dfdad55)

def sig3116 : Sig := (0x42250b056602000a81020c08210504a32617204c22f40100a10322990cd98c00, 0x16e042089900000002c088000900980040cc042008240000a102009108910844)

def sig3127 : Sig := (0x53f71b15eeeeb17aabf63db9fd9f8cffbfdf3b5d7ffd7f3bef3feefb7cdb9ccc, 0xffefcafffffedbfddfffffefef7fffccffdfff3fefb6ff7bef3bffff7dffbddd)

def sig3128 : Sig := (0x4010000000301000102000c01888080108100000004c30ec00e0f800d80000, 0x6608201bd04987c06401502a02b27008fcde0334196c830e800f0fc00fc0055)

def sig3129 : Sig := (0x73f75f15efeff1fbabf63fb9ffdfcdffbfdfff7d7ffdff3bfd33fefd6cfd8cff, 0xffedc2bdfff6dbfd47ffbdefeb7bbfc4ffcff737ebb6ff7bed33fffd6dfdad55)

def sig3130 : Sig := (0x420300102882004821400011050400f20c1022516a84703b0000ee0000d98c00, 0x80040015226409d9410c2424000a2384830032144112e03a0000ff00006ca500)

def sig3131 : Sig := (0x5bff1bfffeeeb97eebf6bdbffd9f8effbfff3bdffffd7f3fed33fff96cffff00, 0xffedc2bdfff6dbfd47ffbdefeb7bbfc4ffcff737ebb6ff7bed33fffd6dfdad55)

def sig3132 : Sig := (0x940001066800008206158008000401b086000014687f000000eef96c000000, 0x9000090422608840431018da05800842000a0004280ff400000772c25000000)

def sig3133 : Sig := (0xd7f7bb15eefeb77abfff7df9fdbfbcffffdf3b5d7fff7ffbed33ffffffd98c00, 0xffedc2bdfff6dbfd47ffbdefeb7bbfc4ffcff737ebb6ff7bed33fffd6dfdad55)

def sig3134 : Sig := (0x11621b14c884b17228f02839f49b885c0b491b1d49117f3bed33000000000000, 0x2809000000000000003100c90000000030020000020017410411000000000000)

def sig3135 : Sig := (0x53f71b15eeeeb17aabf63db9fd9f8cffbfdf3b5d7ffd7fffffffeef96cd98c00, 0xfffdc2bdfff7ffff67ffbdeffb7bbfc6ffeff737ebb6fffffd77fffd6dfdad55)

def sig3136 : Sig := (0x11900000806c81200aa411a01882000490c0090015090228c130cce160c18000, 0x94a00005a940d24041009822412397400b885600a8260028c12088c140e1a050)

def sig3138 : Sig := (0x53f71b15eeeeb17aabf63db9fd9f8cffbfdf3b5d7ffd7f3beff3eefbecfbecf0, 0xffeff6fdfff6dbfdc7fffdefebfffff4ffcfffbfeffeff7befb3ffffedffedf5)

def sig4184 : Sig := (0xbddaf4fa99fdfff57efdf3f7defafb5cd9e8dfb3dd0bfeff5cf0dd64e3246333, 0xe91db5b566f7ffff653f35fff2fb27f7bf23f3d7f3dbffff5cf5ff6ce76ce733)

def sig4185 : Sig := (0xac08e4ea11114e855409c246026073004020c4a2800280c410c0110483246333, 0x103500000124022000001010800033002000c01049008410c4000082004222)

def sig4196 : Sig := (0xbddaf4fa99fdfff57efdf3f7defafb5cd9e8dfb3dd0bfeff5efcdd66f32673ff, 0xe91fbdf766fffffffd3f77fff6ff67ffbf33fbdff7dbffff5efdff6ef76ef7bb)

def sig4197 : Sig := (0x204054000101709100102200c258c9080108d4200000cc305c00d06400240033, 0x80012404987c04001502a02b27008f01e0134192c8304800f06c006c0011)

def sig4198 : Sig := (0xbddaf4fa99fdfff57efdf3f7defafb5cd9e8dfb3dd0bfefffcf0fdfce3fc63ff, 0xef7db7b5fff7ffff677f35fff2fb27f7bfeff3f7f3dffffffcf5fffce7fce777)

def sig4199 : Sig := (0x80a00fa18800844604080170400025008200293c800703f0000dd0000246300, 0x80040015226409d9410c2424000a2384830032144112e03a0000ff00006ca500)

def sig4200 : Sig := (0xffdbf4fab9fffffd7ffdf3f7dffefbfeddf8fff3ff8ffeff5cf0ff64e3ffff33, 0xe91db5b566f7ffff653f35fff2fb27f7bf23f3d7f3dbffff5cf5ff6ce76ce733)

def sig4201 : Sig := (0x8490a00000780600160d51c008203000d0800000140a7ec00000dd64e3000000, 0x9000090422608840431018da05800842000a0004280ff400000772c25000000)

def sig4202 : Sig := (0xbddef4fb9ffdfff5fefff7f7defaff5df9eedfb3dd6bffff5cf0ffffff246333, 0xe91db5b566f7ffff653f35fff2fb27f7bf23f3d7f3dbffff5cf5ff6ce76ce733)

def sig4203 : Sig := (0x114210108884b17028f02031d49a885c09481b1149017eff5cf0000000000000, 0x2819000000012402203100c91000000230220000020017c51455000000000000)

def sig4204 : Sig := (0xbdfafffed9fdfff77efdfbfffefbfb5cdbe9dfbfdd1bffffffffdd64e3246333, 0xe91db5b566f7ffff653f35fff2fb27f7bf23f3d7f3dbffff5cf5ff6ce76ce733)

def sig4205 : Sig := (0x11900000806c81200aa411a01882000490c009001509022840f0cc60e0206030, 0x800034052040d2404100102240a307700b005280a04a002840a08840c060e030)

def sig4225 : Sig := (0xbddaf4fa99fdfff57efdf3f7defafb5cd9e8dfb3dd0bfeffdff0dde7e3e7e3f3, 0xfdbfb5f5eff7ffffe53ffdfff3fff7f7bfabffdfffffffffdff5ffefe7efe7f3)

def sig5354 : Sig := (0xee6fffff7f937edff55bee5fe77dfffb6f3ff6ffeaf6fdd73c0f331c1f1c1f0f, 0x6b5dcbba56bf2dbf3eff27ddbe58288ff477a1775391ffd73c5f773c3f1c1f0f)

def sig5355 : Sig := (0xac08e4ea11114e855409c246026073004020c4a2800280c4100c11041304130f, 0x10090200092402380002101400000b0030004010010084104c00001200120a)

def sig5356 : Sig := (0xee6fffff7f937edff55bee5fe77dfffb6f3ff6ffeaf6fdd73ecf331e9f3e7fff, 0x6b5ffffa56bf2dbfbeff67ddbedc68bff477a9ff57d9ffd73edf773ebf1e5faf)

def sig5357 : Sig := (0x42250b056602000a81020c08210504a32617204c22f40100200f22181c181c0c, 0x2404a0a100800001ac002000c0008084054002000000000200a00101810180c)

def sig5358 : Sig := (0xee6fffff7f937edff55bee5fe77dfffb6f3ff6ffeaf6fdd7bf0f339f1fdf9fcf, 0x7fffcbfadfbf2dbfbeffefddbf5cf88ff4ffad7f5fb5ffd7bf5f77bf3f9f1fcf)

def sig5359 : Sig := (0x204054000101709100102200c258c9080108d4200000cc103c00301c001c000f, 0x24082001404083c06400500a00820008445a0334190c8102800703c001c0005)

def sig5360 : Sig := (0xee6fffff7f937edff55bee5fe77dfffb6f3ff6ffeaf6fdf7fc0ff3fc1ffc1fff, 0x6f7dcbbbffbfbdff3eff37dfbe7b2f8fffffe1775397fff7fc5ff7fc3ffc1f5f)

def sig5361 : Sig := (0x4a0b00fa3882084c61408017050402f20c3022d3ea84701700003300001c1f00, 0x4001002240999000c240400082084800020144110e01200007700000c0500)

def sig5362 : Sig := (0xee6fffff7f937edff55bee5fe77dfffb6f3ff6ffeaf6fdff3c0fff1c1fffff0f, 0xeb5dcbbf76ff2dff7fff27fdbe5a2b8ff777b3775393ffff3c5fff3c3f7cbf0f)

def sig5363 : Sig := (0x8404a00106100600940b4440002034016006000000627dc00000331c1f000000, 0x9000090422608840431018da05800842000a0004280ff400000772c25000000)

def sig5364 : Sig := (0xeeffffff7ffb7edff75fffdfef7dfffbffbff6fffefeffd73c0fffffff1c1f0f, 0x6b5dcbba56bf2dbf3eff27ddbe58288ff477a1775391ffd73c5f773c3f1c1f0f)

def sig5365 : Sig := (0x621b144880305220502819e41988580b09121d48107dd73c0f000000000000, 0x2819000000012402203100c91000000230220000020017c51455000000000000)

def sig5366 : Sig := (0xff6fffffff97fffffdfbee7ff7ffffff6f7fffffebf7ffffffff331c1f1c1f0f, 0x6b5dcbba56bf2dbf3eff27ddbe58288ff477a1775391ffd73c5f773c3f1c1f0f)

def sig6416 : Sig := (0xdfbfabfffefe8f6effefddff3da736f7fef72bdfffff33cf03ff0f03ff03ff00, 0xf99f7dfe42fb6783f9bfeafd5fd4d8ff70321fccbe6937cf17ff0f03ff03ffaa)

def sig6417 : Sig := (0x8c08a0ea10100e045409c0460020320040200082800200c402cc010293027300, 0x123d4200092402b80042101484403b003008c81449008412cc0002920252aa)

def sig6418 : Sig := (0xffbfefffffffcfefffefdfff3fe777f7fef7efffffffb3cf13ff1f07ff27ffff, 0xf99f7dfe42fb6783f9bfeafd5fd4d8ff70321fccbe6937cf17ff0f03ff03ffaa)

def sig6419 : Sig := (0x42250b056602000a81020c08210504a32617204c22f40100030f02031c039c00, 0x1082484a000800009880ca000d04d80840100c080c200000030a000318031888)

def sig6420 : Sig := (0xdfbfabfffefe8f6effefddff3da736f7fef72bdfffff33cfa3ff2f9bffdbffcc, 0xffff7ffedbfb6783fbffeafd5fd4d8ff70fe1fecbe6d37cfb7ff0f93ff93ffee)

def sig6421 : Sig := (0x4a0b00fa3882084c61408017050402f20c3022d3ea84300f00000f000003ff00, 0x8004001402600181410c202400000084000012040000200a00000f000000a500)

def sig6422 : Sig := (0xdfbfabfffefe8f6effefddff3da736f7fef72bdfffff73ff03ffff03ffffff00, 0xf99f7dff62ff6fdbf9bfeefd5fdefbfff3323fdcff7bf7ff17ffff03ff6fffaa)

def sig6423 : Sig := (0x8494a00106780600960f55c008203401f0860000146a33c000000f03ff000000, 0x9000090422200800031008d0050008420000000020037400000070025000000)

def sig6424 : Sig := (0xdfbfabfffefe8f6effefddff3da736f7fef72bdfffff7fcf03ffffffff03ff00, 0xf99f7dfe42ff6f87fdbfebfdffdcd8ff7032bfccfee9ffcf17ff7f2fff03ffaa)

def sig6425 : Sig := (0x11220b14c884816228e00839348300540a410b1d491133cf03ff000000000000, 0x2819000000012402203100c91000000230220000020017c51455000000000000)

def sig6426 : Sig := (0xdfffbbfffefebf7efffffdfffdbfbeffffff3bdfffff7fffffff0f03ff03ff00, 0xf99f7dfe42fb6783f9bfeafd5fd4d8ff70321fccbe6937cf17ff0f03ff03ffaa)

def sig6429 : Sig := (0x11900000806c81200aa411a01882000490c009001509020803f00c03e003e000, 0x9082344400404200c100c8204184d07000001e88ac68000803a00803c003e0a0)

def sig6430 : Sig := (0xdfbfabfffefe8f6effefddff3da736f7fef72bdfffff33efc3ffcfe3ffe3fff0, 0xfdbf7dffebfbf7c3f9bffaff5ff7dfff7bba5fccbe6f37efd7ff8fc3ffe3fffa)

def sig7478 : Sig := (0xb5f4ff05c77df7b39ebf7fe8fafbfd0df3cfdd2c157b8fc0ffff00ffff0000ff, 0x7ffbffeadd9bf626bef3dbdbfff5dc7b7cffcdebbeed1fc5ffff00ffff935aff)

def sig7479 : Sig := (0xa400e4000111468114094240026071004000c420000280c012cc0006930000ff, 0x123d4200092402b80042101484403b003008c81449008412cc0002920252aa)

def sig7480 : Sig := (0xbdfcffefd77dffb7debfffeefafbff0df3efddae957b8fc4ffff11ffff2673ff, 0x7ffbffeadd9bf626bef3dbdbfff5dc7b7cffcdebbeed1fc5ffff00ffff935aff)

def sig7481 : Sig := (0x240b054600000280020c08200104012207000c00700100a30f009b1c0000cc, 0x16e24a4a990800009ac0ca000d04d80840dc0c280c240000a30a0093189318cc)

def sig7482 : Sig := (0xf7f5ff05e77ff7bb9fbf7fe8fbfffdaff7dffd6c37ff8fc0ffff22ffffdb9cff, 0x7ffbffeadd9bf626bef3dbdbfff5dc7b7cffcdebbeed1fc5ffff00ffff935aff)

def sig7483 : Sig := (0x204054000101709100102200c258c9080108d42000008c00fc0000fc000000ff, 0x66082009d00902406401102a02104000ccdc02300840800e80000fc00900055)

def sig7494 : Sig := (0xb5f4ff05c77df7b39ebf7fe8fafbfd0df3cfdd2c157bcff0fffff0fffffc00ff, 0x7ffbffebfd9ffe7ebef3dfdbffffff7bffffedfbffffdff5fffff0ffffff5aff)

def sig7495 : Sig := (0x8494a00106780600960f55c008203401f0860000146a0fc0000000ffff000000, 0x90000804002000404310189a05000002000800002801f400000002c25000000)

def sig7496 : Sig := (0xb5f4ff05c77df7b39ebf7fe8fafbfd0df3cfdd2c157bffc0ffffffffff0000ff, 0x7ffbfffadfbffea6bef3dbdffffddcff7cffedebfeedffc5ffff77ffff935aff)

def sig7497 : Sig := (0x11601b04c004b13208b02828f09b880c0349190c01110fc0ffff000000000000, 0x2819000000012402203100c91000000230220000020017c51455000000000000)

def sig7498 : Sig := (0xb5f6ff15cffdf7f3beff7ff9fefbfd5dfbcfdf3d5d7bffffffff00ffff0000ff, 0x7ffbffeadd9bf626bef3dbdbfff5dc7b7cffcdebbeed1fc5ffff00ffff935aff)

def sig7501 : Sig := (0x11900000806c81200aa411a01882000490c0090015090200c3f000e3e00000f0, 0x14a234408900d2008000d80241a5d47008884c88ac6c0000c3a000c3c08340f0)

def sig7502 : Sig := (0xb5f4ff05c77df7b39ebf7fe8fafbfd0df3cfdd2c157b8fe8ffffccffffe3e0ff, 0xfffbffeffddbf666fff3dbfbfff7df7b7fffdfebbeef1fedffff88fffff3faff)

def sig8648 : Sig := (0x7b6b5ffef987f9ff69f0aa3ff7dfcbfe0f79ffffeb95803fffff000000ffffff, 0xf6ffff6fbdd9f77bfbcefe725fa7ff7bdfff5fffbd7f00bfffff88d3daffffff)

def sig8649 : Sig := (0x280844ea1101488540008206024043000020c4a28000800412cc0000002673ff, 0x123d4200092402b80042101484403b003008c81449008412cc0002920252aa)

def sig8650 : Sig := (0xff6bfffef997ffff7df9ea7ff7fffbfe4f79ffffeb9780ffffff110693ffffff, 0xf6ffff6fbdd9f77bfbcefe725fa7ff7bdfff5fffbd7f00bfffff88d3daffffff)

def sig8651 : Sig := (0x42210b046002000a01000808210500a20611204c22940000a30f000000db9ccc, 0x16e24a4a990800009ac0ca000d04d80840dc0c280c240000a30a0093189318cc)

def sig8652 : Sig := (0x7b6f5fffff87f9ffe9f2ae3ff7dfcfff2f7fffffebf5813fffff229b1cffffff, 0xf6ffff6fbdd9f77bfbcefe725fa7ff7bdfff5fffbd7f00bfffff88d3daffffff)

def sig8653 : Sig := (0x204054000101709100102200c258c9080108d42000008030fc00000000fc00ff, 0x6608201bd00907802401402002327008fcd403301160030e80080d000fc0055)

def sig8654 : Sig := (0x7b6b5ffef987f9ff69f0aa3ff7dfcbfe0f79ffffeb95cc3ffffff0fc00ffffff, 0xf6ffff6fbdddff7fffceff72ffafff7bdffffffffdffc8bffffff8ffdaffffff)

def sig8655 : Sig := (0x4a0b00fa3882084c61408017050402f20c3022d3ea84003f0000000000ffff00, 0x8004000520400159410c242000022300830012140112003a00008800006ca500)

def sig8656 : Sig := (0x7b6b5ffef987f9ff69f0aa3ff7dfcbfe0f79ffffeb95f03fffffff0000ffffff, 0xf6ffff7fbffdfffbfbcefe765fafffffdfff7ffffd7fe0bfffffffd3daffffff)

def sig8657 : Sig := (0x11621b14c884b17228f02839f49b885c0b491b1d4911003fffff000000000000, 0x2019000000012402200000401000000210220000000000851455000000000000)

def sig8658 : Sig := (0x7b6b5ffef987f9ff69f0aa3ff7dfcbfe0f79ffffeb95ffffffff000000ffffff, 0xfeffff6fbdd9f77bfbfffefb5fa7ff7bffff5fffbf7f17ffffff88d3daffffff)

def sig8661 : Sig := (0x110000008004812008a00020108200040040090001010028c3f0000000e3e0f0, 0x94a23445a940d240c100d82241a7d7700b885e88ac6e0028c3a088c3c0e3e0f0)

def sig8662 : Sig := (0x7bfb5ffef9eff9ff6bf4bbbfffdfcbfe9ff9ffffff9d823fffffcce3e0ffffff, 0xf6ffff6fbdd9f77bfbcefe725fa7ff7bdfff5fffbd7f00bfffff88d3daffffff)

def sig9717 : Sig := (0xee9de4eb377b4e8dd70fd7c60b6477a3f4b6e4e2b6ee80000000ffffffffffff, 0xd7e6fffffffedbfddfceff36effffffdcfddfffffdffe83aebaaffffffffffff)

def sig9718 : Sig := (0xac08e4ea11114e855409c246026073004020c4a28002800000001106932673ff, 0x23d42000800009800421004844039001008c81449000002880002920252aa)

def sig9719 : Sig := (0xee9de4eb377b4e8dd70fd7c60b6477a3f4b6e4e2b6ee80c412ccffffffffffff, 0xd7f6ffffffffffffffceff36ffffffffcffdfffffdffe8befbeeffffffffffff)

def sig9720 : Sig := (0x420500012602000881020400010404a32416204022e400000000229b1cdb9ccc, 0x16e24a4a990800009ac0ca000d04d80840dc0c280c240000a30a0093189318cc)

def sig9721 : Sig := (0xeebdefef777b4e8fd70fdfce2b6577a3f6b7e4eeb6fe8100a30fffffffffffff, 0xd7e6fffffffedbfddfceff36effffffdcfddfffffdffe83aebaaffffffffffff)

def sig9722 : Sig := (0x200044000101408100000200024041000000c420000080000000f0fc00fc00ff, 0x6608201bd04987c06401502a02b27008fcde0334196c830e800f0fc00fc0055)

def sig9723 : Sig := (0xeeddf4eb377b7e9dd71ff7c6cb7cffabf5bef4e2b6eecc30fc00ffffffffffff, 0xd7e6fffffffedbfddfceff36effffffdcfddfffffdffe83aebaaffffffffffff)

def sig9724 : Sig := (0x4a0900ea3002080c41008006010402a2043020c2a28400000000ff0000ffff00, 0x80040015226409d9410c2424000a2384830032144112e03a0000ff00006ca500)

def sig9725 : Sig := (0xee9fe4fb3ffb4ecdf74fd7d70f6477f3fcb6e6f3feeef03f0000ffffffffffff, 0xd7e6fffffffedbfddfceff36effffffdcfddfffffdffe83aebaaffffffffffff)

def sig9726 : Sig := (0x8494a00106780600960f55c008203401f0860000146a00000000ffffff000000, 0x10000904226088404000104a05800840000a0004080e8000000772c25000000)

def sig9727 : Sig := (0xee9de4eb377b4e8dd70fd7c60b6477a3f4b6e4e2b6eeffc00000ffffffffffff, 0xdfe6fffffffedbfddfffffbfeffffffdefddffffffffff7aebaaffffffffffff)

def sig9730 : Sig := (0x90000000680000020411800800000090800000140800000000cce3e0e3e0f0, 0x94a23445a940d240c100d82241a7d7700b885e88ac6e0028c3a088c3c0e3e0f0)

def sig9731 : Sig := (0xff9de4ebb77fcfaddfafd7e61be677a7f4f6ede2b7ef8228c3f0ffffffffffff, 0xd7e6fffffffedbfddfceff36effffffdcfddfffffdffe83aebaaffffffffffff)

def sig10757 : Sig := (0xac4af4fa19917ed57459e257c678fb584928d6b3c802fcd71c00110403040303, 0x691d81b046b72dbf243f25ddb2582087b423a1575391ffd71c55772c270c0703)

def sig10787 : Sig := (0x95b4ab05c67c87229eaf5de838a33405f2c7090c157b03c003ff0003ff000000, 0x799b7dea409b6602b8b3cad95fd4d87b70320dc8be6917c517ff0003ff035aaa)

def sig10819 : Sig := (0xac08e4ea11114e855409c246026073004020c4a2800280c412cc1106932463ff, 0x123d4200092402b80042101484403b003008c81449008412cc0002920252aa)

def sig11013 : Sig := (0xdfffbbfffefebf7efffffdfffdbfbeffffff3bdfffff7fffefffeffbffdbff00, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)

def sig11570 : Sig := (0xeeffffff7ffb7edff75fffdfef7dfffbffbff6fffefefdd73c0fffffffffffff, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)

def sig11811 : Sig := (0xffbfefffffffcfefffefdfff3fe777f7fef7efffffffb3cf03ffffffffffffff, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)

def sig12436 : Sig := (0x7bff5fffffeff9ffebf6bfbfffdfcfffbffffffffffdff3fffffeef96cffffff, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)

def sig13160 : Sig := (0x11900000806c81200aa411a01882000490c0090015090228c3f0cce3e02060f0, 0x94a23445a940d240c100d82241a7d7700b885e88ac6e0028c3a088c3c0e3e0f0)

def sig13368 : Sig := (0xbdfeffffdffdfff7fefffffffefbff5dfbefdfbfdd7bffffffffddffff2463ff, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)

def sig13369 : Sig := (0x8494a00106780600960f55c008203401f0860000146a7fc00000ddffff000000, 0x9000090422608840431018da05800842000a0004280ff400000772c25000000)

def sig13379 : Sig := (0x204054000101709100102200c258c9080108d4200000cc30fc00d0fc002400ff, 0x6608201bd04987c06401502a02b27008fcde0334196c830e800f0fc00fc0055)

def sig13882 : Sig := (0xff6fffffff97fffffdfbee7ff7ffffff6f7fffffebf7fdffffff331c1fffffff, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)

def bank0 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig10]

def bank1 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig11]

def bank2 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig12]

def bank3 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig13]

def bank4 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig14]

def bank5 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig15]

def bank6 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig16]

def bank7 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig17]

def bank8 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig18]

def bank9 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig19]

def bank10 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig20]

def bank11 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig21]

def bank12 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig22]

def bank13 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23]

def bank14 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig23]

def bank15 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig26]

def bank16 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig27]

def bank17 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig48]

def bank18 : List Sig := [sig4, sig5, sig6, sig7, sig8, sig9, sig280]

def bank19 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig280]

def bank20 : List Sig := [sig4, sig5, sig6, sig7, sig8, sig9, sig28, sig280]

def bank21 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig23, sig28]

def bank22 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig28]

def bank23 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig9, sig23, sig28]

def bank24 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig1447]

def bank25 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig1848]

def bank26 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig1848]

def bank27 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig28, sig1848]

def bank28 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig28, sig35]

def bank29 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig9, sig28, sig35]

def bank30 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig28, sig35]

def bank31 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig1549]

def bank32 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig1565]

def bank33 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig1565]

def bank34 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig28, sig1565]

def bank35 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig1555]

def bank36 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig9, sig1556]

def bank37 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig1556]

def bank38 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig9, sig28, sig1556]

def bank39 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig1560]

def bank40 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig1560]

def bank41 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig28, sig1560]

def bank42 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig28]

def bank43 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig29]

def bank44 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig30]

def bank45 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig31]

def bank46 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig32]

def bank47 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig33]

def bank48 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig62]

def bank49 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig63]

def bank50 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig64]

def bank51 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig65]

def bank52 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig66]

def bank53 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig67]

def bank54 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig68]

def bank55 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig69]

def bank56 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig34]

def bank57 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35]

def bank58 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig35]

def bank59 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig36]

def bank60 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig37]

def bank61 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig38]

def bank62 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig39]

def bank63 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig44]

def bank64 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig45]

def bank65 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig46]

def bank66 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig47]

def bank67 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig52]

def bank68 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig53]

def bank69 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9]

def bank70 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig10, sig3115]

def bank71 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig11, sig3115]

def bank72 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig12, sig3115]

def bank73 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig13, sig3115]

def bank74 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig14, sig3115]

def bank75 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig15, sig3115]

def bank76 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig16, sig3115]

def bank77 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig17, sig3115]

def bank78 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig18, sig3115]

def bank79 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig19, sig3115]

def bank80 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig20, sig3115]

def bank81 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig21, sig3115]

def bank82 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig22, sig3115]

def bank83 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig3115]

def bank84 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig23, sig3115]

def bank85 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig26, sig3115]

def bank86 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig27, sig3115]

def bank87 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig28, sig3115]

def bank88 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig29, sig3115]

def bank89 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig30, sig3115]

def bank90 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig31, sig3115]

def bank91 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig32, sig3115]

def bank92 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig33, sig3115]

def bank93 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3116]

def bank94 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3115, sig3116]

def bank95 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3127]

def bank96 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3115, sig3127]

def bank97 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig62, sig3115]

def bank98 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig63, sig3115]

def bank99 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig64, sig3115]

def bank100 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig65, sig3115]

def bank101 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig66, sig3115]

def bank102 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig67, sig3115]

def bank103 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig68, sig3115]

def bank104 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig69, sig3115]

def bank105 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3136]

def bank106 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3115, sig3136]

def bank107 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3138]

def bank108 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3115, sig3138]

def bank109 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig34, sig3115]

def bank110 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig3115]

def bank111 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig35, sig3115]

def bank112 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig36, sig3115]

def bank113 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig37, sig3115]

def bank114 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig38, sig3115]

def bank115 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig39, sig3115]

def bank116 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3128]

def bank117 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3115, sig3128]

def bank118 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3129]

def bank119 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3115, sig3129]

def bank120 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig44, sig3115]

def bank121 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig45, sig3115]

def bank122 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig46, sig3115]

def bank123 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig47, sig3115]

def bank124 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3130]

def bank125 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3115, sig3130]

def bank126 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3131]

def bank127 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3115, sig3131]

def bank128 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig52, sig3115]

def bank129 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig53, sig3115]

def bank130 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3132]

def bank131 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3115, sig3132]

def bank132 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3133]

def bank133 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3115, sig3133]

def bank134 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3134]

def bank135 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3115, sig3134]

def bank136 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3135]

def bank137 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3115, sig3135]

def bank138 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig3115]

def bank139 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig10, sig4184]

def bank140 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig11, sig4184]

def bank141 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig12, sig4184]

def bank142 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig13, sig4184]

def bank143 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig14, sig4184]

def bank144 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig15, sig4184]

def bank145 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig16, sig4184]

def bank146 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig17, sig4184]

def bank147 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig18, sig4184]

def bank148 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig19, sig4184]

def bank149 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig20, sig4184]

def bank150 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig21, sig4184]

def bank151 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4185]

def bank152 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4184, sig4185]

def bank153 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4196]

def bank154 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4184, sig4196]

def bank155 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig22, sig4184]

def bank156 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig4184]

def bank157 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig23, sig4184]

def bank158 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig26, sig4184]

def bank159 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig27, sig4184]

def bank160 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig28, sig4184]

def bank161 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig29, sig4184]

def bank162 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig30, sig4184]

def bank163 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig31, sig4184]

def bank164 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig32, sig4184]

def bank165 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig33, sig4184]

def bank166 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig62, sig4184]

def bank167 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig63, sig4184]

def bank168 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig64, sig4184]

def bank169 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig65, sig4184]

def bank170 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig66, sig4184]

def bank171 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig67, sig4184]

def bank172 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig68, sig4184]

def bank173 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig69, sig4184]

def bank174 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig4205]

def bank175 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4205]

def bank176 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig4184, sig4205]

def bank177 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4184, sig4205]

def bank178 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4225]

def bank179 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4184, sig4225]

def bank180 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig34, sig4184]

def bank181 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig4184]

def bank182 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig35, sig4184]

def bank183 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig36, sig4184]

def bank184 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig37, sig4184]

def bank185 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig38, sig4184]

def bank186 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig39, sig4184]

def bank187 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4197]

def bank188 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4184, sig4197]

def bank189 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4198]

def bank190 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4184, sig4198]

def bank191 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig44, sig4184]

def bank192 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig45, sig4184]

def bank193 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig46, sig4184]

def bank194 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig47, sig4184]

def bank195 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4199]

def bank196 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4184, sig4199]

def bank197 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4200]

def bank198 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4184, sig4200]

def bank199 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig52, sig4184]

def bank200 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig53, sig4184]

def bank201 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4201]

def bank202 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4184, sig4201]

def bank203 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4202]

def bank204 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4184, sig4202]

def bank205 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4203]

def bank206 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4184, sig4203]

def bank207 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4204]

def bank208 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4184, sig4204]

def bank209 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig4184]

def bank210 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig10, sig5354]

def bank211 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig11, sig5354]

def bank212 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig12, sig5354]

def bank213 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig13, sig5354]

def bank214 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig14, sig5354]

def bank215 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig15, sig5354]

def bank216 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig16, sig5354]

def bank217 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig17, sig5354]

def bank218 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig18, sig5354]

def bank219 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig19, sig5354]

def bank220 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig20, sig5354]

def bank221 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig21, sig5354]

def bank222 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5355]

def bank223 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5354, sig5355]

def bank224 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5356]

def bank225 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5354, sig5356]

def bank226 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig22, sig5354]

def bank227 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig5354]

def bank228 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig23, sig5354]

def bank229 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig26, sig5354]

def bank230 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig27, sig5354]

def bank231 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig28, sig5354]

def bank232 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig29, sig5354]

def bank233 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig30, sig5354]

def bank234 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig31, sig5354]

def bank235 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig32, sig5354]

def bank236 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig33, sig5354]

def bank237 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5357]

def bank238 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5354, sig5357]

def bank239 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5358]

def bank240 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5354, sig5358]

def bank241 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig62, sig5354]

def bank242 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig63, sig5354]

def bank243 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig64, sig5354]

def bank244 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig65, sig5354]

def bank245 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig66, sig5354]

def bank246 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig67, sig5354]

def bank247 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig68, sig5354]

def bank248 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig69, sig5354]

def bank249 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig34, sig5354]

def bank250 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig5354]

def bank251 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig35, sig5354]

def bank252 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig36, sig5354]

def bank253 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig37, sig5354]

def bank254 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig38, sig5354]

def bank255 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig39, sig5354]

def bank256 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5359]

def bank257 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5354, sig5359]

def bank258 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5360]

def bank259 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5354, sig5360]

def bank260 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig44, sig5354]

def bank261 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig45, sig5354]

def bank262 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig46, sig5354]

def bank263 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig47, sig5354]

def bank264 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5361]

def bank265 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5354, sig5361]

def bank266 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5362]

def bank267 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5354, sig5362]

def bank268 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig52, sig5354]

def bank269 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig53, sig5354]

def bank270 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5363]

def bank271 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5354, sig5363]

def bank272 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5364]

def bank273 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5354, sig5364]

def bank274 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5365]

def bank275 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5354, sig5365]

def bank276 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5366]

def bank277 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5354, sig5366]

def bank278 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig5354]

def bank279 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig10, sig6416]

def bank280 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig11, sig6416]

def bank281 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig12, sig6416]

def bank282 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig13, sig6416]

def bank283 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig14, sig6416]

def bank284 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig15, sig6416]

def bank285 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig16, sig6416]

def bank286 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig17, sig6416]

def bank287 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig18, sig6416]

def bank288 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig19, sig6416]

def bank289 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig20, sig6416]

def bank290 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig21, sig6416]

def bank291 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6417]

def bank292 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6416, sig6417]

def bank293 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6418]

def bank294 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6416, sig6418]

def bank295 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig22, sig6416]

def bank296 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig6416]

def bank297 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig23, sig6416]

def bank298 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig26, sig6416]

def bank299 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig27, sig6416]

def bank300 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig28, sig6416]

def bank301 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig29, sig6416]

def bank302 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig30, sig6416]

def bank303 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig31, sig6416]

def bank304 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig32, sig6416]

def bank305 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig33, sig6416]

def bank306 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6419]

def bank307 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6416, sig6419]

def bank308 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6420]

def bank309 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6416, sig6420]

def bank310 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig62, sig6416]

def bank311 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig63, sig6416]

def bank312 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig64, sig6416]

def bank313 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig65, sig6416]

def bank314 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig66, sig6416]

def bank315 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig67, sig6416]

def bank316 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig68, sig6416]

def bank317 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig69, sig6416]

def bank318 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6429]

def bank319 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6416, sig6429]

def bank320 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6430]

def bank321 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6416, sig6430]

def bank322 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig34, sig6416]

def bank323 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig6416]

def bank324 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig35, sig6416]

def bank325 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig36, sig6416]

def bank326 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig37, sig6416]

def bank327 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig38, sig6416]

def bank328 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig39, sig6416]

def bank329 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig44, sig6416]

def bank330 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig45, sig6416]

def bank331 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig46, sig6416]

def bank332 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig47, sig6416]

def bank333 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6421]

def bank334 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6416, sig6421]

def bank335 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6422]

def bank336 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6416, sig6422]

def bank337 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig52, sig6416]

def bank338 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig53, sig6416]

def bank339 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6423]

def bank340 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6416, sig6423]

def bank341 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6424]

def bank342 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6416, sig6424]

def bank343 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6425]

def bank344 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6416, sig6425]

def bank345 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6426]

def bank346 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6416, sig6426]

def bank347 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig6416]

def bank348 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig10, sig7478]

def bank349 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig11, sig7478]

def bank350 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig12, sig7478]

def bank351 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig13, sig7478]

def bank352 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig14, sig7478]

def bank353 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig15, sig7478]

def bank354 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig16, sig7478]

def bank355 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig17, sig7478]

def bank356 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig18, sig7478]

def bank357 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig19, sig7478]

def bank358 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig20, sig7478]

def bank359 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig21, sig7478]

def bank360 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7479]

def bank361 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7478, sig7479]

def bank362 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7480]

def bank363 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7478, sig7480]

def bank364 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig22, sig7478]

def bank365 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig7478]

def bank366 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig23, sig7478]

def bank367 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig26, sig7478]

def bank368 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig27, sig7478]

def bank369 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig28, sig7478]

def bank370 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig29, sig7478]

def bank371 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig30, sig7478]

def bank372 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig31, sig7478]

def bank373 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig32, sig7478]

def bank374 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig33, sig7478]

def bank375 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7481]

def bank376 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7478, sig7481]

def bank377 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7482]

def bank378 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7478, sig7482]

def bank379 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig62, sig7478]

def bank380 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig63, sig7478]

def bank381 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig64, sig7478]

def bank382 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig65, sig7478]

def bank383 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig66, sig7478]

def bank384 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig67, sig7478]

def bank385 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig68, sig7478]

def bank386 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig69, sig7478]

def bank387 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7501]

def bank388 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7478, sig7501]

def bank389 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7502]

def bank390 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7478, sig7502]

def bank391 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig34, sig7478]

def bank392 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig7478]

def bank393 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig35, sig7478]

def bank394 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig36, sig7478]

def bank395 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig37, sig7478]

def bank396 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig38, sig7478]

def bank397 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig39, sig7478]

def bank398 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig7483]

def bank399 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7483]

def bank400 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig7478, sig7483]

def bank401 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7478, sig7483]

def bank402 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7494]

def bank403 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7478, sig7494]

def bank404 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig44, sig7478]

def bank405 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig45, sig7478]

def bank406 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig46, sig7478]

def bank407 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig47, sig7478]

def bank408 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig52, sig7478]

def bank409 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig53, sig7478]

def bank410 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7495]

def bank411 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7478, sig7495]

def bank412 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7496]

def bank413 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7478, sig7496]

def bank414 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7497]

def bank415 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7478, sig7497]

def bank416 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7498]

def bank417 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7478, sig7498]

def bank418 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig7478]

def bank419 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig10, sig8648]

def bank420 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig11, sig8648]

def bank421 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig12, sig8648]

def bank422 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig13, sig8648]

def bank423 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig14, sig8648]

def bank424 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig15, sig8648]

def bank425 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig16, sig8648]

def bank426 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig17, sig8648]

def bank427 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig18, sig8648]

def bank428 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig19, sig8648]

def bank429 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig20, sig8648]

def bank430 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig21, sig8648]

def bank431 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8649]

def bank432 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8648, sig8649]

def bank433 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8650]

def bank434 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8648, sig8650]

def bank435 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig22, sig8648]

def bank436 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig8648]

def bank437 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig23, sig8648]

def bank438 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig26, sig8648]

def bank439 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig27, sig8648]

def bank440 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig28, sig8648]

def bank441 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig29, sig8648]

def bank442 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig30, sig8648]

def bank443 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig31, sig8648]

def bank444 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig32, sig8648]

def bank445 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig33, sig8648]

def bank446 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8651]

def bank447 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8648, sig8651]

def bank448 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8652]

def bank449 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8648, sig8652]

def bank450 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig62, sig8648]

def bank451 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig63, sig8648]

def bank452 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig64, sig8648]

def bank453 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig65, sig8648]

def bank454 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig66, sig8648]

def bank455 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig67, sig8648]

def bank456 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig68, sig8648]

def bank457 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig69, sig8648]

def bank458 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8661]

def bank459 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8648, sig8661]

def bank460 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8662]

def bank461 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8648, sig8662]

def bank462 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig34, sig8648]

def bank463 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig8648]

def bank464 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig35, sig8648]

def bank465 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig36, sig8648]

def bank466 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig37, sig8648]

def bank467 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig38, sig8648]

def bank468 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig39, sig8648]

def bank469 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8653]

def bank470 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8648, sig8653]

def bank471 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8654]

def bank472 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8648, sig8654]

def bank473 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig44, sig8648]

def bank474 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig45, sig8648]

def bank475 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig46, sig8648]

def bank476 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig47, sig8648]

def bank477 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8655]

def bank478 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8648, sig8655]

def bank479 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8656]

def bank480 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8648, sig8656]

def bank481 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig52, sig8648]

def bank482 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig53, sig8648]

def bank483 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8657]

def bank484 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8648, sig8657]

def bank485 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8658]

def bank486 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8648, sig8658]

def bank487 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig8648]

def bank488 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig10, sig9717]

def bank489 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig11, sig9717]

def bank490 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig12, sig9717]

def bank491 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig13, sig9717]

def bank492 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig14, sig9717]

def bank493 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig15, sig9717]

def bank494 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig16, sig9717]

def bank495 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig17, sig9717]

def bank496 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig18, sig9717]

def bank497 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig19, sig9717]

def bank498 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig20, sig9717]

def bank499 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig21, sig9717]

def bank500 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9718]

def bank501 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9717, sig9718]

def bank502 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9719]

def bank503 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9717, sig9719]

def bank504 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig22, sig9717]

def bank505 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig9717]

def bank506 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig23, sig9717]

def bank507 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig26, sig9717]

def bank508 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig27, sig9717]

def bank509 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig28, sig9717]

def bank510 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig29, sig9717]

def bank511 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig30, sig9717]

def bank512 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig31, sig9717]

def bank513 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig32, sig9717]

def bank514 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig33, sig9717]

def bank515 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9720]

def bank516 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9717, sig9720]

def bank517 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9721]

def bank518 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9717, sig9721]

def bank519 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig62, sig9717]

def bank520 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig63, sig9717]

def bank521 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig64, sig9717]

def bank522 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig65, sig9717]

def bank523 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig66, sig9717]

def bank524 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig67, sig9717]

def bank525 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig68, sig9717]

def bank526 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig69, sig9717]

def bank527 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9730]

def bank528 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9717, sig9730]

def bank529 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9731]

def bank530 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9717, sig9731]

def bank531 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig34, sig9717]

def bank532 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig9717]

def bank533 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig35, sig9717]

def bank534 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig36, sig9717]

def bank535 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig37, sig9717]

def bank536 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig38, sig9717]

def bank537 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig39, sig9717]

def bank538 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9722]

def bank539 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9717, sig9722]

def bank540 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9723]

def bank541 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9717, sig9723]

def bank542 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig44, sig9717]

def bank543 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig45, sig9717]

def bank544 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig46, sig9717]

def bank545 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig47, sig9717]

def bank546 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9724]

def bank547 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9717, sig9724]

def bank548 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9725]

def bank549 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9717, sig9725]

def bank550 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig52, sig9717]

def bank551 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig53, sig9717]

def bank552 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9726]

def bank553 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9717, sig9726]

def bank554 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9727]

def bank555 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9717, sig9727]

def bank556 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig9717]

def bank557 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig11013]

def bank558 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig14, sig11013]

def bank559 : List Sig := [sig4, sig5, sig6, sig7, sig8, sig9, sig11, sig14]

def bank560 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig14, sig15]

def bank561 : List Sig := [sig4, sig5, sig6, sig7, sig8, sig9, sig14, sig15]

def bank562 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig14, sig23]

def bank563 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig14, sig27]

def bank564 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig40]

def bank565 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig9, sig264]

def bank566 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig264]

def bank567 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig9, sig14, sig264]

def bank568 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig14, sig63]

def bank569 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig255]

def bank570 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig256]

def bank571 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig256]

def bank572 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig14, sig256]

def bank573 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig14, sig35]

def bank574 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig14, sig38]

def bank575 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig220]

def bank576 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig9, sig221]

def bank577 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig221]

def bank578 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig9, sig14, sig221]

def bank579 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig235]

def bank580 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig9, sig236]

def bank581 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig236]

def bank582 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig9, sig14, sig236]

def bank583 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig244]

def bank584 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig245]

def bank585 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig245]

def bank586 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig14, sig245]

def bank587 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig12436]

def bank588 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig18, sig12436]

def bank589 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig9, sig18, sig19]

def bank590 : List Sig := [sig4, sig5, sig6, sig7, sig8, sig9, sig18, sig19]

def bank591 : List Sig := [sig4, sig5, sig6, sig7, sig8, sig9, sig18, sig21]

def bank592 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig18, sig23]

def bank593 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig54]

def bank594 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig9, sig423]

def bank595 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig423]

def bank596 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig9, sig18, sig423]

def bank597 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig568]

def bank598 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig738]

def bank599 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig738]

def bank600 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig18, sig738]

def bank601 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig18, sig35]

def bank602 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig1017]

def bank603 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig1017]

def bank604 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig18, sig1017]

def bank605 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig1065]

def bank606 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig9, sig1189]

def bank607 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig1189]

def bank608 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig9, sig18, sig1189]

def bank609 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig9, sig18, sig53]

def bank610 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig1228]

def bank611 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig1221]

def bank612 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig1221]

def bank613 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig18, sig1221]

def bank614 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig10757]

def bank615 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig10, sig23]

def bank616 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig11, sig23]

def bank617 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig11, sig23]

def bank618 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig15, sig23]

def bank619 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig16, sig23]

def bank620 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig17, sig23]

def bank621 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig19, sig23]

def bank622 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig20, sig23]

def bank623 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig21, sig23]

def bank624 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig24]

def bank625 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig25]

def bank626 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig26]

def bank627 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig27]

def bank628 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig23, sig28, sig3115]

def bank629 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig23, sig28, sig6416]

def bank630 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig23, sig28, sig7478]

def bank631 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig23, sig28, sig8648]

def bank632 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig23, sig28, sig9717]

def bank633 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig23, sig28, sig10757]

def bank634 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig23, sig28, sig13368]

def bank635 : List Sig := [sig6, sig7, sig8, sig9, sig23, sig280]

def bank636 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig23, sig280]

def bank637 : List Sig := [sig6, sig7, sig8, sig9, sig23, sig28, sig280]

def bank638 : List Sig := [sig3, sig8, sig9, sig23, sig28, sig35]

def bank639 : List Sig := [sig3, sig6, sig8, sig9, sig23, sig28, sig35]

def bank640 : List Sig := [sig3, sig7, sig8, sig9, sig23, sig28, sig35]

def bank641 : List Sig := [sig3, sig7, sig8, sig9, sig23, sig28, sig1565]

def bank642 : List Sig := [sig3, sig6, sig7, sig9, sig23, sig1556]

def bank643 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig23, sig1556]

def bank644 : List Sig := [sig3, sig6, sig7, sig9, sig23, sig28, sig1556]

def bank645 : List Sig := [sig3, sig6, sig7, sig8, sig23, sig1560]

def bank646 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig23, sig1560]

def bank647 : List Sig := [sig3, sig6, sig7, sig8, sig23, sig28, sig1560]

def bank648 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig29]

def bank649 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig30]

def bank650 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig23, sig31]

def bank651 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig31]

def bank652 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig32]

def bank653 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig23, sig33]

def bank654 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig33]

def bank655 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig34]

def bank656 : List Sig := [sig3, sig4, sig7, sig8, sig9, sig23, sig35]

def bank657 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig35]

def bank658 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig36]

def bank659 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig37]

def bank660 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig38]

def bank661 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig39]

def bank662 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig42]

def bank663 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig43]

def bank664 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig44]

def bank665 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig45]

def bank666 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig46]

def bank667 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig47]

def bank668 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig50]

def bank669 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig51]

def bank670 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig52]

def bank671 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig53]

def bank672 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig56]

def bank673 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig57]

def bank674 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig60]

def bank675 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig61]

def bank676 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig13368]

def bank677 : List Sig := [sig4, sig5, sig6, sig7, sig8, sig9, sig280, sig13368]

def bank678 : List Sig := [sig4, sig5, sig6, sig7, sig8, sig9, sig28, sig10819]

def bank679 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig9, sig28, sig7481]

def bank680 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig1848, sig13368]

def bank681 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig28, sig13160]

def bank682 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig28, sig35, sig13368]

def bank683 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig1565, sig13368]

def bank684 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig28, sig13379]

def bank685 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig9, sig28, sig4199]

def bank686 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig9, sig1556, sig13368]

def bank687 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig9, sig28, sig13369]

def bank688 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig1560, sig13368]

def bank689 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig28, sig13368]

def bank690 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig9, sig28, sig29]

def bank691 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig9, sig28, sig29]

def bank692 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig28, sig35, sig3115]

def bank693 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig28, sig35, sig4184]

def bank694 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig28, sig35, sig5354]

def bank695 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig28, sig35, sig8648]

def bank696 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig28, sig35, sig9717]

def bank697 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig28, sig35, sig10787]

def bank698 : List Sig := [sig4, sig5, sig8, sig9, sig35, sig280]

def bank699 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig35, sig280]

def bank700 : List Sig := [sig4, sig5, sig8, sig9, sig28, sig35, sig280]

def bank701 : List Sig := [sig3, sig4, sig8, sig9, sig23, sig28, sig35]

def bank702 : List Sig := [sig3, sig5, sig8, sig9, sig23, sig28, sig35]

def bank703 : List Sig := [sig3, sig4, sig8, sig9, sig28, sig35, sig1848]

def bank704 : List Sig := [sig3, sig4, sig5, sig9, sig35, sig1556]

def bank705 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig35, sig1556]

def bank706 : List Sig := [sig3, sig4, sig5, sig9, sig28, sig35, sig1556]

def bank707 : List Sig := [sig3, sig4, sig5, sig8, sig35, sig1560]

def bank708 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig35, sig1560]

def bank709 : List Sig := [sig3, sig4, sig5, sig8, sig28, sig35, sig1560]

def bank710 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig13882]

def bank711 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig66, sig13882]

def bank712 : List Sig := [sig4, sig5, sig6, sig7, sig8, sig9, sig689]

def bank713 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig689]

def bank714 : List Sig := [sig4, sig5, sig6, sig7, sig8, sig9, sig66, sig689]

def bank715 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig66]

def bank716 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig1449]

def bank717 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig9, sig1594]

def bank718 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig1594]

def bank719 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig9, sig66, sig1594]

def bank720 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig63, sig66]

def bank721 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig65, sig66]

def bank722 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig9, sig66, sig67]

def bank723 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig66, sig67]

def bank724 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig66, sig68]

def bank725 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig66]

def bank726 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig1853]

def bank727 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig1882]

def bank728 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig1882]

def bank729 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig66, sig1882]

def bank730 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig9, sig45, sig66]

def bank731 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig1868]

def bank732 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig9, sig1888]

def bank733 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig1888]

def bank734 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig9, sig66, sig1888]

def bank735 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig768]

def bank736 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig1893]

def bank737 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig1893]

def bank738 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig66, sig1893]

def bank739 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig11570]

def bank740 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig68, sig11570]

def bank741 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig13, sig68]

def bank742 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig570]

def bank743 : List Sig := [sig4, sig5, sig6, sig7, sig8, sig9, sig698]

def bank744 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig698]

def bank745 : List Sig := [sig4, sig5, sig6, sig7, sig8, sig9, sig68, sig698]

def bank746 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig23, sig68]

def bank747 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig432]

def bank748 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig9, sig745]

def bank749 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig745]

def bank750 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig9, sig68, sig745]

def bank751 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig68, sig69]

def bank752 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig68, sig69]

def bank753 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig68]

def bank754 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig753]

def bank755 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig754]

def bank756 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig754]

def bank757 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig68, sig754]

def bank758 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig761]

def bank759 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig9, sig762]

def bank760 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig762]

def bank761 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig9, sig68, sig762]

def bank762 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig9, sig769]

def bank763 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig769]

def bank764 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig9, sig68, sig769]

def bank765 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig10787]

def bank766 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig10, sig35]

def bank767 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig11, sig35]

def bank768 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig12, sig35]

def bank769 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig13, sig35]

def bank770 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig16, sig35]

def bank771 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig17, sig35]

def bank772 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig17, sig35]

def bank773 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig19, sig35]

def bank774 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig20, sig35]

def bank775 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig21, sig35]

def bank776 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig81]

def bank777 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig82]

def bank778 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig22, sig35]

def bank779 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig23, sig35]

def bank780 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig29, sig35]

def bank781 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig30, sig35]

def bank782 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig31, sig35]

def bank783 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig32, sig35]

def bank784 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig33, sig35]

def bank785 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig83]

def bank786 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig84]

def bank787 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig64]

def bank788 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig65]

def bank789 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig67]

def bank790 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig69]

def bank791 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig99]

def bank792 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig100]

def bank793 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig44]

def bank794 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig35, sig45]

def bank795 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig45]

def bank796 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig46]

def bank797 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig35, sig47]

def bank798 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig47]

def bank799 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig52]

def bank800 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig53]

def bank801 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig87]

def bank802 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig88]

def bank803 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig91]

def bank804 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig92]

def bank805 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig11811]

def bank806 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig38, sig11811]

def bank807 : List Sig := [sig4, sig5, sig6, sig7, sig8, sig9, sig875]

def bank808 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig875]

def bank809 : List Sig := [sig4, sig5, sig6, sig7, sig8, sig9, sig38, sig875]

def bank810 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig440]

def bank811 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig9, sig876]

def bank812 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig876]

def bank813 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig9, sig38, sig876]

def bank814 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig888]

def bank815 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig888]

def bank816 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig38, sig888]

def bank817 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig35, sig38]

def bank818 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig37, sig38]

def bank819 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig38, sig39]

def bank820 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig38, sig39]

def bank821 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig904]

def bank822 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig9, sig905]

def bank823 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig905]

def bank824 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig9, sig38, sig905]

def bank825 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig900]

def bank826 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig9, sig901]

def bank827 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig901]

def bank828 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig9, sig38, sig901]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded0 : Blocked 8 0 bank0 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded1 : Blocked 8 0 bank1 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded2 : Blocked 8 0 bank2 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded3 : Blocked 8 0 bank3 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded4 : Blocked 8 0 bank4 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded5 : Blocked 8 0 bank5 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded6 : Blocked 8 0 bank6 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded7 : Blocked 8 0 bank7 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded8 : Blocked 8 0 bank8 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded9 : Blocked 8 0 bank9 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded10 : Blocked 8 0 bank10 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded11 : Blocked 8 0 bank11 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded12 : Blocked 8 0 bank12 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded13 : Blocked 8 0 bank13 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded14 : Blocked 8 0 bank14 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded15 : Blocked 8 0 bank15 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded16 : Blocked 8 0 bank16 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded17 : Blocked 7 0 bank17 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded18 : Blocked 7 0 bank18 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded19 : Blocked 7 0 bank19 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded20 : Blocked 7 0 bank20 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded21 : Blocked 7 0 bank21 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded22 : Blocked 7 0 bank22 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded23 : Blocked 7 0 bank23 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded24 : Blocked 7 0 bank24 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded25 : Blocked 7 0 bank25 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded26 : Blocked 7 0 bank26 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded27 : Blocked 7 0 bank27 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded28 : Blocked 7 0 bank28 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded29 : Blocked 7 0 bank29 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded30 : Blocked 7 0 bank30 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded31 : Blocked 7 0 bank31 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded32 : Blocked 7 0 bank32 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded33 : Blocked 7 0 bank33 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded34 : Blocked 7 0 bank34 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded35 : Blocked 7 0 bank35 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded36 : Blocked 7 0 bank36 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded37 : Blocked 7 0 bank37 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded38 : Blocked 7 0 bank38 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded39 : Blocked 7 0 bank39 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded40 : Blocked 7 0 bank40 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded41 : Blocked 7 0 bank41 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded42 : Blocked 8 0 bank42 :=
  block_step [] [bank17, bank18, bank19, bank20, bank21, bank22, bank23, bank24, bank25, bank26, bank27, bank28, bank29, bank30, bank31, bank32, bank33, bank34, bank35, bank36, bank37, bank38, bank39, bank40, bank41]
    True.intro
    ⟨excluded17, excluded18, excluded19, excluded20, excluded21, excluded22, excluded23, excluded24, excluded25, excluded26, excluded27, excluded28, excluded29, excluded30, excluded31, excluded32, excluded33, excluded34, excluded35, excluded36, excluded37, excluded38, excluded39, excluded40, excluded41, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded43 : Blocked 8 0 bank43 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded44 : Blocked 8 0 bank44 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded45 : Blocked 8 0 bank45 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded46 : Blocked 8 0 bank46 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded47 : Blocked 8 0 bank47 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded48 : Blocked 8 0 bank48 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded49 : Blocked 8 0 bank49 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded50 : Blocked 8 0 bank50 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded51 : Blocked 8 0 bank51 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded52 : Blocked 8 0 bank52 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded53 : Blocked 8 0 bank53 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded54 : Blocked 8 0 bank54 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded55 : Blocked 8 0 bank55 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded56 : Blocked 8 0 bank56 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded57 : Blocked 8 0 bank57 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded58 : Blocked 8 0 bank58 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded59 : Blocked 8 0 bank59 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded60 : Blocked 8 0 bank60 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded61 : Blocked 8 0 bank61 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded62 : Blocked 8 0 bank62 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded63 : Blocked 8 0 bank63 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded64 : Blocked 8 0 bank64 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded65 : Blocked 8 0 bank65 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded66 : Blocked 8 0 bank66 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded67 : Blocked 8 0 bank67 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded68 : Blocked 8 0 bank68 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded69 : Blocked 9 0 bank69 :=
  block_step [] [bank0, bank1, bank2, bank3, bank4, bank5, bank6, bank7, bank8, bank9, bank10, bank11, bank12, bank13, bank14, bank15, bank16, bank42, bank43, bank44, bank45, bank46, bank47, bank48, bank49, bank50, bank51, bank52, bank53, bank54, bank55, bank56, bank57, bank58, bank59, bank60, bank61, bank62, bank63, bank64, bank65, bank66, bank67, bank68]
    True.intro
    ⟨excluded0, excluded1, excluded2, excluded3, excluded4, excluded5, excluded6, excluded7, excluded8, excluded9, excluded10, excluded11, excluded12, excluded13, excluded14, excluded15, excluded16, excluded42, excluded43, excluded44, excluded45, excluded46, excluded47, excluded48, excluded49, excluded50, excluded51, excluded52, excluded53, excluded54, excluded55, excluded56, excluded57, excluded58, excluded59, excluded60, excluded61, excluded62, excluded63, excluded64, excluded65, excluded66, excluded67, excluded68, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded70 : Blocked 8 0 bank70 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded71 : Blocked 8 0 bank71 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded72 : Blocked 8 0 bank72 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded73 : Blocked 8 0 bank73 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded74 : Blocked 8 0 bank74 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded75 : Blocked 8 0 bank75 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded76 : Blocked 8 0 bank76 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded77 : Blocked 8 0 bank77 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded78 : Blocked 8 0 bank78 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded79 : Blocked 8 0 bank79 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded80 : Blocked 8 0 bank80 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded81 : Blocked 8 0 bank81 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded82 : Blocked 8 0 bank82 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded83 : Blocked 8 0 bank83 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded84 : Blocked 8 0 bank84 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded85 : Blocked 8 0 bank85 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded86 : Blocked 8 0 bank86 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded87 : Blocked 8 0 bank87 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded88 : Blocked 8 0 bank88 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded89 : Blocked 8 0 bank89 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded90 : Blocked 8 0 bank90 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded91 : Blocked 8 0 bank91 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded92 : Blocked 8 0 bank92 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded93 : Blocked 8 0 bank93 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded94 : Blocked 8 0 bank94 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded95 : Blocked 8 0 bank95 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded96 : Blocked 8 0 bank96 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded97 : Blocked 8 0 bank97 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded98 : Blocked 8 0 bank98 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded99 : Blocked 8 0 bank99 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded100 : Blocked 8 0 bank100 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded101 : Blocked 8 0 bank101 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded102 : Blocked 8 0 bank102 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded103 : Blocked 8 0 bank103 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded104 : Blocked 8 0 bank104 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded105 : Blocked 8 0 bank105 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded106 : Blocked 8 0 bank106 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded107 : Blocked 8 0 bank107 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded108 : Blocked 8 0 bank108 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded109 : Blocked 8 0 bank109 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded110 : Blocked 8 0 bank110 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded111 : Blocked 8 0 bank111 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded112 : Blocked 8 0 bank112 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded113 : Blocked 8 0 bank113 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded114 : Blocked 8 0 bank114 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded115 : Blocked 8 0 bank115 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded116 : Blocked 8 0 bank116 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded117 : Blocked 8 0 bank117 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded118 : Blocked 8 0 bank118 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded119 : Blocked 8 0 bank119 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded120 : Blocked 8 0 bank120 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded121 : Blocked 8 0 bank121 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded122 : Blocked 8 0 bank122 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded123 : Blocked 8 0 bank123 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded124 : Blocked 8 0 bank124 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded125 : Blocked 8 0 bank125 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded126 : Blocked 8 0 bank126 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded127 : Blocked 8 0 bank127 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded128 : Blocked 8 0 bank128 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded129 : Blocked 8 0 bank129 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded130 : Blocked 8 0 bank130 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded131 : Blocked 8 0 bank131 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded132 : Blocked 8 0 bank132 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded133 : Blocked 8 0 bank133 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded134 : Blocked 8 0 bank134 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded135 : Blocked 8 0 bank135 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded136 : Blocked 8 0 bank136 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded137 : Blocked 8 0 bank137 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded138 : Blocked 9 0 bank138 :=
  block_step [] [bank70, bank71, bank72, bank73, bank74, bank75, bank76, bank77, bank78, bank79, bank80, bank81, bank82, bank83, bank84, bank85, bank86, bank87, bank88, bank89, bank90, bank91, bank92, bank93, bank94, bank95, bank96, bank97, bank98, bank99, bank100, bank101, bank102, bank103, bank104, bank105, bank106, bank107, bank108, bank109, bank110, bank111, bank112, bank113, bank114, bank115, bank116, bank117, bank118, bank119, bank120, bank121, bank122, bank123, bank124, bank125, bank126, bank127, bank128, bank129, bank130, bank131, bank132, bank133, bank134, bank135, bank136, bank137]
    True.intro
    ⟨excluded70, excluded71, excluded72, excluded73, excluded74, excluded75, excluded76, excluded77, excluded78, excluded79, excluded80, excluded81, excluded82, excluded83, excluded84, excluded85, excluded86, excluded87, excluded88, excluded89, excluded90, excluded91, excluded92, excluded93, excluded94, excluded95, excluded96, excluded97, excluded98, excluded99, excluded100, excluded101, excluded102, excluded103, excluded104, excluded105, excluded106, excluded107, excluded108, excluded109, excluded110, excluded111, excluded112, excluded113, excluded114, excluded115, excluded116, excluded117, excluded118, excluded119, excluded120, excluded121, excluded122, excluded123, excluded124, excluded125, excluded126, excluded127, excluded128, excluded129, excluded130, excluded131, excluded132, excluded133, excluded134, excluded135, excluded136, excluded137, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded139 : Blocked 8 0 bank139 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded140 : Blocked 8 0 bank140 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded141 : Blocked 8 0 bank141 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded142 : Blocked 8 0 bank142 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded143 : Blocked 8 0 bank143 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded144 : Blocked 8 0 bank144 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded145 : Blocked 8 0 bank145 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded146 : Blocked 8 0 bank146 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded147 : Blocked 8 0 bank147 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded148 : Blocked 8 0 bank148 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded149 : Blocked 8 0 bank149 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded150 : Blocked 8 0 bank150 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded151 : Blocked 8 0 bank151 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded152 : Blocked 8 0 bank152 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded153 : Blocked 8 0 bank153 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded154 : Blocked 8 0 bank154 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded155 : Blocked 8 0 bank155 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded156 : Blocked 8 0 bank156 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded157 : Blocked 8 0 bank157 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded158 : Blocked 8 0 bank158 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded159 : Blocked 8 0 bank159 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded160 : Blocked 8 0 bank160 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded161 : Blocked 8 0 bank161 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded162 : Blocked 8 0 bank162 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded163 : Blocked 8 0 bank163 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded164 : Blocked 8 0 bank164 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded165 : Blocked 8 0 bank165 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded166 : Blocked 8 0 bank166 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded167 : Blocked 8 0 bank167 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded168 : Blocked 8 0 bank168 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded169 : Blocked 8 0 bank169 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded170 : Blocked 8 0 bank170 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded171 : Blocked 8 0 bank171 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded172 : Blocked 8 0 bank172 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded173 : Blocked 8 0 bank173 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded174 : Blocked 8 0 bank174 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded175 : Blocked 8 0 bank175 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded176 : Blocked 8 0 bank176 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded177 : Blocked 8 0 bank177 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded178 : Blocked 8 0 bank178 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded179 : Blocked 8 0 bank179 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded180 : Blocked 8 0 bank180 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded181 : Blocked 8 0 bank181 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded182 : Blocked 8 0 bank182 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded183 : Blocked 8 0 bank183 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded184 : Blocked 8 0 bank184 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded185 : Blocked 8 0 bank185 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded186 : Blocked 8 0 bank186 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded187 : Blocked 8 0 bank187 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded188 : Blocked 8 0 bank188 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded189 : Blocked 8 0 bank189 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded190 : Blocked 8 0 bank190 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded191 : Blocked 8 0 bank191 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded192 : Blocked 8 0 bank192 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded193 : Blocked 8 0 bank193 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded194 : Blocked 8 0 bank194 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded195 : Blocked 8 0 bank195 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded196 : Blocked 8 0 bank196 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded197 : Blocked 8 0 bank197 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded198 : Blocked 8 0 bank198 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded199 : Blocked 8 0 bank199 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded200 : Blocked 8 0 bank200 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded201 : Blocked 8 0 bank201 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded202 : Blocked 8 0 bank202 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded203 : Blocked 8 0 bank203 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded204 : Blocked 8 0 bank204 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded205 : Blocked 8 0 bank205 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded206 : Blocked 8 0 bank206 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded207 : Blocked 8 0 bank207 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded208 : Blocked 8 0 bank208 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded209 : Blocked 9 0 bank209 :=
  block_step [] [bank139, bank140, bank141, bank142, bank143, bank144, bank145, bank146, bank147, bank148, bank149, bank150, bank151, bank152, bank153, bank154, bank155, bank156, bank157, bank158, bank159, bank160, bank161, bank162, bank163, bank164, bank165, bank166, bank167, bank168, bank169, bank170, bank171, bank172, bank173, bank174, bank175, bank176, bank177, bank178, bank179, bank180, bank181, bank182, bank183, bank184, bank185, bank186, bank187, bank188, bank189, bank190, bank191, bank192, bank193, bank194, bank195, bank196, bank197, bank198, bank199, bank200, bank201, bank202, bank203, bank204, bank205, bank206, bank207, bank208]
    True.intro
    ⟨excluded139, excluded140, excluded141, excluded142, excluded143, excluded144, excluded145, excluded146, excluded147, excluded148, excluded149, excluded150, excluded151, excluded152, excluded153, excluded154, excluded155, excluded156, excluded157, excluded158, excluded159, excluded160, excluded161, excluded162, excluded163, excluded164, excluded165, excluded166, excluded167, excluded168, excluded169, excluded170, excluded171, excluded172, excluded173, excluded174, excluded175, excluded176, excluded177, excluded178, excluded179, excluded180, excluded181, excluded182, excluded183, excluded184, excluded185, excluded186, excluded187, excluded188, excluded189, excluded190, excluded191, excluded192, excluded193, excluded194, excluded195, excluded196, excluded197, excluded198, excluded199, excluded200, excluded201, excluded202, excluded203, excluded204, excluded205, excluded206, excluded207, excluded208, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded210 : Blocked 8 0 bank210 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded211 : Blocked 8 0 bank211 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded212 : Blocked 8 0 bank212 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded213 : Blocked 8 0 bank213 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded214 : Blocked 8 0 bank214 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded215 : Blocked 8 0 bank215 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded216 : Blocked 8 0 bank216 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded217 : Blocked 8 0 bank217 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded218 : Blocked 8 0 bank218 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded219 : Blocked 8 0 bank219 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded220 : Blocked 8 0 bank220 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded221 : Blocked 8 0 bank221 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded222 : Blocked 8 0 bank222 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded223 : Blocked 8 0 bank223 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded224 : Blocked 8 0 bank224 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded225 : Blocked 8 0 bank225 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded226 : Blocked 8 0 bank226 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded227 : Blocked 8 0 bank227 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded228 : Blocked 8 0 bank228 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded229 : Blocked 8 0 bank229 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded230 : Blocked 8 0 bank230 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded231 : Blocked 8 0 bank231 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded232 : Blocked 8 0 bank232 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded233 : Blocked 8 0 bank233 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded234 : Blocked 8 0 bank234 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded235 : Blocked 8 0 bank235 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded236 : Blocked 8 0 bank236 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded237 : Blocked 8 0 bank237 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded238 : Blocked 8 0 bank238 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded239 : Blocked 8 0 bank239 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded240 : Blocked 8 0 bank240 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded241 : Blocked 8 0 bank241 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded242 : Blocked 8 0 bank242 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded243 : Blocked 8 0 bank243 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded244 : Blocked 8 0 bank244 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded245 : Blocked 8 0 bank245 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded246 : Blocked 8 0 bank246 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded247 : Blocked 8 0 bank247 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded248 : Blocked 8 0 bank248 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded249 : Blocked 8 0 bank249 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded250 : Blocked 8 0 bank250 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded251 : Blocked 8 0 bank251 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded252 : Blocked 8 0 bank252 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded253 : Blocked 8 0 bank253 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded254 : Blocked 8 0 bank254 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded255 : Blocked 8 0 bank255 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded256 : Blocked 8 0 bank256 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded257 : Blocked 8 0 bank257 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded258 : Blocked 8 0 bank258 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded259 : Blocked 8 0 bank259 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded260 : Blocked 8 0 bank260 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded261 : Blocked 8 0 bank261 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded262 : Blocked 8 0 bank262 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded263 : Blocked 8 0 bank263 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded264 : Blocked 8 0 bank264 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded265 : Blocked 8 0 bank265 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded266 : Blocked 8 0 bank266 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded267 : Blocked 8 0 bank267 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded268 : Blocked 8 0 bank268 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded269 : Blocked 8 0 bank269 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded270 : Blocked 8 0 bank270 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded271 : Blocked 8 0 bank271 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded272 : Blocked 8 0 bank272 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded273 : Blocked 8 0 bank273 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded274 : Blocked 8 0 bank274 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded275 : Blocked 8 0 bank275 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded276 : Blocked 8 0 bank276 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded277 : Blocked 8 0 bank277 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded278 : Blocked 9 0 bank278 :=
  block_step [] [bank210, bank211, bank212, bank213, bank214, bank215, bank216, bank217, bank218, bank219, bank220, bank221, bank222, bank223, bank224, bank225, bank226, bank227, bank228, bank229, bank230, bank231, bank232, bank233, bank234, bank235, bank236, bank237, bank238, bank239, bank240, bank241, bank242, bank243, bank244, bank245, bank246, bank247, bank248, bank249, bank250, bank251, bank252, bank253, bank254, bank255, bank256, bank257, bank258, bank259, bank260, bank261, bank262, bank263, bank264, bank265, bank266, bank267, bank268, bank269, bank270, bank271, bank272, bank273, bank274, bank275, bank276, bank277]
    True.intro
    ⟨excluded210, excluded211, excluded212, excluded213, excluded214, excluded215, excluded216, excluded217, excluded218, excluded219, excluded220, excluded221, excluded222, excluded223, excluded224, excluded225, excluded226, excluded227, excluded228, excluded229, excluded230, excluded231, excluded232, excluded233, excluded234, excluded235, excluded236, excluded237, excluded238, excluded239, excluded240, excluded241, excluded242, excluded243, excluded244, excluded245, excluded246, excluded247, excluded248, excluded249, excluded250, excluded251, excluded252, excluded253, excluded254, excluded255, excluded256, excluded257, excluded258, excluded259, excluded260, excluded261, excluded262, excluded263, excluded264, excluded265, excluded266, excluded267, excluded268, excluded269, excluded270, excluded271, excluded272, excluded273, excluded274, excluded275, excluded276, excluded277, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded279 : Blocked 8 0 bank279 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded280 : Blocked 8 0 bank280 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded281 : Blocked 8 0 bank281 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded282 : Blocked 8 0 bank282 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded283 : Blocked 8 0 bank283 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded284 : Blocked 8 0 bank284 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded285 : Blocked 8 0 bank285 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded286 : Blocked 8 0 bank286 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded287 : Blocked 8 0 bank287 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded288 : Blocked 8 0 bank288 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded289 : Blocked 8 0 bank289 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded290 : Blocked 8 0 bank290 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded291 : Blocked 8 0 bank291 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded292 : Blocked 8 0 bank292 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded293 : Blocked 8 0 bank293 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded294 : Blocked 8 0 bank294 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded295 : Blocked 8 0 bank295 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded296 : Blocked 8 0 bank296 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded297 : Blocked 8 0 bank297 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded298 : Blocked 8 0 bank298 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded299 : Blocked 8 0 bank299 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded300 : Blocked 8 0 bank300 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded301 : Blocked 8 0 bank301 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded302 : Blocked 8 0 bank302 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded303 : Blocked 8 0 bank303 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded304 : Blocked 8 0 bank304 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded305 : Blocked 8 0 bank305 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded306 : Blocked 8 0 bank306 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded307 : Blocked 8 0 bank307 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded308 : Blocked 8 0 bank308 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded309 : Blocked 8 0 bank309 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded310 : Blocked 8 0 bank310 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded311 : Blocked 8 0 bank311 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded312 : Blocked 8 0 bank312 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded313 : Blocked 8 0 bank313 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded314 : Blocked 8 0 bank314 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded315 : Blocked 8 0 bank315 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded316 : Blocked 8 0 bank316 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded317 : Blocked 8 0 bank317 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded318 : Blocked 8 0 bank318 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded319 : Blocked 8 0 bank319 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded320 : Blocked 8 0 bank320 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded321 : Blocked 8 0 bank321 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded322 : Blocked 8 0 bank322 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded323 : Blocked 8 0 bank323 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded324 : Blocked 8 0 bank324 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded325 : Blocked 8 0 bank325 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded326 : Blocked 8 0 bank326 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded327 : Blocked 8 0 bank327 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded328 : Blocked 8 0 bank328 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded329 : Blocked 8 0 bank329 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded330 : Blocked 8 0 bank330 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded331 : Blocked 8 0 bank331 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded332 : Blocked 8 0 bank332 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded333 : Blocked 8 0 bank333 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded334 : Blocked 8 0 bank334 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded335 : Blocked 8 0 bank335 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded336 : Blocked 8 0 bank336 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded337 : Blocked 8 0 bank337 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded338 : Blocked 8 0 bank338 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded339 : Blocked 8 0 bank339 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded340 : Blocked 8 0 bank340 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded341 : Blocked 8 0 bank341 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded342 : Blocked 8 0 bank342 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded343 : Blocked 8 0 bank343 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded344 : Blocked 8 0 bank344 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded345 : Blocked 8 0 bank345 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded346 : Blocked 8 0 bank346 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded347 : Blocked 9 0 bank347 :=
  block_step [] [bank279, bank280, bank281, bank282, bank283, bank284, bank285, bank286, bank287, bank288, bank289, bank290, bank291, bank292, bank293, bank294, bank295, bank296, bank297, bank298, bank299, bank300, bank301, bank302, bank303, bank304, bank305, bank306, bank307, bank308, bank309, bank310, bank311, bank312, bank313, bank314, bank315, bank316, bank317, bank318, bank319, bank320, bank321, bank322, bank323, bank324, bank325, bank326, bank327, bank328, bank329, bank330, bank331, bank332, bank333, bank334, bank335, bank336, bank337, bank338, bank339, bank340, bank341, bank342, bank343, bank344, bank345, bank346]
    True.intro
    ⟨excluded279, excluded280, excluded281, excluded282, excluded283, excluded284, excluded285, excluded286, excluded287, excluded288, excluded289, excluded290, excluded291, excluded292, excluded293, excluded294, excluded295, excluded296, excluded297, excluded298, excluded299, excluded300, excluded301, excluded302, excluded303, excluded304, excluded305, excluded306, excluded307, excluded308, excluded309, excluded310, excluded311, excluded312, excluded313, excluded314, excluded315, excluded316, excluded317, excluded318, excluded319, excluded320, excluded321, excluded322, excluded323, excluded324, excluded325, excluded326, excluded327, excluded328, excluded329, excluded330, excluded331, excluded332, excluded333, excluded334, excluded335, excluded336, excluded337, excluded338, excluded339, excluded340, excluded341, excluded342, excluded343, excluded344, excluded345, excluded346, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded348 : Blocked 8 0 bank348 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded349 : Blocked 8 0 bank349 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded350 : Blocked 8 0 bank350 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded351 : Blocked 8 0 bank351 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded352 : Blocked 8 0 bank352 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded353 : Blocked 8 0 bank353 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded354 : Blocked 8 0 bank354 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded355 : Blocked 8 0 bank355 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded356 : Blocked 8 0 bank356 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded357 : Blocked 8 0 bank357 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded358 : Blocked 8 0 bank358 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded359 : Blocked 8 0 bank359 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded360 : Blocked 8 0 bank360 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded361 : Blocked 8 0 bank361 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded362 : Blocked 8 0 bank362 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded363 : Blocked 8 0 bank363 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded364 : Blocked 8 0 bank364 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded365 : Blocked 8 0 bank365 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded366 : Blocked 8 0 bank366 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded367 : Blocked 8 0 bank367 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded368 : Blocked 8 0 bank368 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded369 : Blocked 8 0 bank369 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded370 : Blocked 8 0 bank370 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded371 : Blocked 8 0 bank371 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded372 : Blocked 8 0 bank372 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded373 : Blocked 8 0 bank373 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded374 : Blocked 8 0 bank374 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded375 : Blocked 8 0 bank375 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded376 : Blocked 8 0 bank376 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded377 : Blocked 8 0 bank377 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded378 : Blocked 8 0 bank378 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded379 : Blocked 8 0 bank379 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded380 : Blocked 8 0 bank380 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded381 : Blocked 8 0 bank381 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded382 : Blocked 8 0 bank382 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded383 : Blocked 8 0 bank383 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded384 : Blocked 8 0 bank384 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded385 : Blocked 8 0 bank385 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded386 : Blocked 8 0 bank386 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded387 : Blocked 8 0 bank387 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded388 : Blocked 8 0 bank388 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded389 : Blocked 8 0 bank389 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded390 : Blocked 8 0 bank390 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded391 : Blocked 8 0 bank391 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded392 : Blocked 8 0 bank392 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded393 : Blocked 8 0 bank393 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded394 : Blocked 8 0 bank394 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded395 : Blocked 8 0 bank395 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded396 : Blocked 8 0 bank396 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded397 : Blocked 8 0 bank397 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded398 : Blocked 8 0 bank398 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded399 : Blocked 8 0 bank399 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded400 : Blocked 8 0 bank400 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded401 : Blocked 8 0 bank401 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded402 : Blocked 8 0 bank402 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded403 : Blocked 8 0 bank403 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded404 : Blocked 8 0 bank404 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded405 : Blocked 8 0 bank405 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded406 : Blocked 8 0 bank406 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded407 : Blocked 8 0 bank407 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded408 : Blocked 8 0 bank408 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded409 : Blocked 8 0 bank409 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded410 : Blocked 8 0 bank410 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded411 : Blocked 8 0 bank411 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded412 : Blocked 8 0 bank412 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded413 : Blocked 8 0 bank413 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded414 : Blocked 8 0 bank414 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded415 : Blocked 8 0 bank415 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded416 : Blocked 8 0 bank416 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded417 : Blocked 8 0 bank417 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded418 : Blocked 9 0 bank418 :=
  block_step [] [bank348, bank349, bank350, bank351, bank352, bank353, bank354, bank355, bank356, bank357, bank358, bank359, bank360, bank361, bank362, bank363, bank364, bank365, bank366, bank367, bank368, bank369, bank370, bank371, bank372, bank373, bank374, bank375, bank376, bank377, bank378, bank379, bank380, bank381, bank382, bank383, bank384, bank385, bank386, bank387, bank388, bank389, bank390, bank391, bank392, bank393, bank394, bank395, bank396, bank397, bank398, bank399, bank400, bank401, bank402, bank403, bank404, bank405, bank406, bank407, bank408, bank409, bank410, bank411, bank412, bank413, bank414, bank415, bank416, bank417]
    True.intro
    ⟨excluded348, excluded349, excluded350, excluded351, excluded352, excluded353, excluded354, excluded355, excluded356, excluded357, excluded358, excluded359, excluded360, excluded361, excluded362, excluded363, excluded364, excluded365, excluded366, excluded367, excluded368, excluded369, excluded370, excluded371, excluded372, excluded373, excluded374, excluded375, excluded376, excluded377, excluded378, excluded379, excluded380, excluded381, excluded382, excluded383, excluded384, excluded385, excluded386, excluded387, excluded388, excluded389, excluded390, excluded391, excluded392, excluded393, excluded394, excluded395, excluded396, excluded397, excluded398, excluded399, excluded400, excluded401, excluded402, excluded403, excluded404, excluded405, excluded406, excluded407, excluded408, excluded409, excluded410, excluded411, excluded412, excluded413, excluded414, excluded415, excluded416, excluded417, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded419 : Blocked 8 0 bank419 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded420 : Blocked 8 0 bank420 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded421 : Blocked 8 0 bank421 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded422 : Blocked 8 0 bank422 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded423 : Blocked 8 0 bank423 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded424 : Blocked 8 0 bank424 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded425 : Blocked 8 0 bank425 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded426 : Blocked 8 0 bank426 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded427 : Blocked 8 0 bank427 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded428 : Blocked 8 0 bank428 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded429 : Blocked 8 0 bank429 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded430 : Blocked 8 0 bank430 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded431 : Blocked 8 0 bank431 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded432 : Blocked 8 0 bank432 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded433 : Blocked 8 0 bank433 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded434 : Blocked 8 0 bank434 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded435 : Blocked 8 0 bank435 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded436 : Blocked 8 0 bank436 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded437 : Blocked 8 0 bank437 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded438 : Blocked 8 0 bank438 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded439 : Blocked 8 0 bank439 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded440 : Blocked 8 0 bank440 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded441 : Blocked 8 0 bank441 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded442 : Blocked 8 0 bank442 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded443 : Blocked 8 0 bank443 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded444 : Blocked 8 0 bank444 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded445 : Blocked 8 0 bank445 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded446 : Blocked 8 0 bank446 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded447 : Blocked 8 0 bank447 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded448 : Blocked 8 0 bank448 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded449 : Blocked 8 0 bank449 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded450 : Blocked 8 0 bank450 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded451 : Blocked 8 0 bank451 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded452 : Blocked 8 0 bank452 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded453 : Blocked 8 0 bank453 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded454 : Blocked 8 0 bank454 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded455 : Blocked 8 0 bank455 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded456 : Blocked 8 0 bank456 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded457 : Blocked 8 0 bank457 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded458 : Blocked 8 0 bank458 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded459 : Blocked 8 0 bank459 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded460 : Blocked 8 0 bank460 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded461 : Blocked 8 0 bank461 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded462 : Blocked 8 0 bank462 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded463 : Blocked 8 0 bank463 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded464 : Blocked 8 0 bank464 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded465 : Blocked 8 0 bank465 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded466 : Blocked 8 0 bank466 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded467 : Blocked 8 0 bank467 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded468 : Blocked 8 0 bank468 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded469 : Blocked 8 0 bank469 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded470 : Blocked 8 0 bank470 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded471 : Blocked 8 0 bank471 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded472 : Blocked 8 0 bank472 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded473 : Blocked 8 0 bank473 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded474 : Blocked 8 0 bank474 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded475 : Blocked 8 0 bank475 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded476 : Blocked 8 0 bank476 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded477 : Blocked 8 0 bank477 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded478 : Blocked 8 0 bank478 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded479 : Blocked 8 0 bank479 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded480 : Blocked 8 0 bank480 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded481 : Blocked 8 0 bank481 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded482 : Blocked 8 0 bank482 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded483 : Blocked 8 0 bank483 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded484 : Blocked 8 0 bank484 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded485 : Blocked 8 0 bank485 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded486 : Blocked 8 0 bank486 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded487 : Blocked 9 0 bank487 :=
  block_step [] [bank419, bank420, bank421, bank422, bank423, bank424, bank425, bank426, bank427, bank428, bank429, bank430, bank431, bank432, bank433, bank434, bank435, bank436, bank437, bank438, bank439, bank440, bank441, bank442, bank443, bank444, bank445, bank446, bank447, bank448, bank449, bank450, bank451, bank452, bank453, bank454, bank455, bank456, bank457, bank458, bank459, bank460, bank461, bank462, bank463, bank464, bank465, bank466, bank467, bank468, bank469, bank470, bank471, bank472, bank473, bank474, bank475, bank476, bank477, bank478, bank479, bank480, bank481, bank482, bank483, bank484, bank485, bank486]
    True.intro
    ⟨excluded419, excluded420, excluded421, excluded422, excluded423, excluded424, excluded425, excluded426, excluded427, excluded428, excluded429, excluded430, excluded431, excluded432, excluded433, excluded434, excluded435, excluded436, excluded437, excluded438, excluded439, excluded440, excluded441, excluded442, excluded443, excluded444, excluded445, excluded446, excluded447, excluded448, excluded449, excluded450, excluded451, excluded452, excluded453, excluded454, excluded455, excluded456, excluded457, excluded458, excluded459, excluded460, excluded461, excluded462, excluded463, excluded464, excluded465, excluded466, excluded467, excluded468, excluded469, excluded470, excluded471, excluded472, excluded473, excluded474, excluded475, excluded476, excluded477, excluded478, excluded479, excluded480, excluded481, excluded482, excluded483, excluded484, excluded485, excluded486, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded488 : Blocked 8 0 bank488 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded489 : Blocked 8 0 bank489 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded490 : Blocked 8 0 bank490 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded491 : Blocked 8 0 bank491 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded492 : Blocked 8 0 bank492 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded493 : Blocked 8 0 bank493 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded494 : Blocked 8 0 bank494 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded495 : Blocked 8 0 bank495 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded496 : Blocked 8 0 bank496 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded497 : Blocked 8 0 bank497 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded498 : Blocked 8 0 bank498 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded499 : Blocked 8 0 bank499 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded500 : Blocked 8 0 bank500 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded501 : Blocked 8 0 bank501 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded502 : Blocked 8 0 bank502 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded503 : Blocked 8 0 bank503 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded504 : Blocked 8 0 bank504 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded505 : Blocked 8 0 bank505 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded506 : Blocked 8 0 bank506 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded507 : Blocked 8 0 bank507 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded508 : Blocked 8 0 bank508 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded509 : Blocked 8 0 bank509 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded510 : Blocked 8 0 bank510 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded511 : Blocked 8 0 bank511 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded512 : Blocked 8 0 bank512 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded513 : Blocked 8 0 bank513 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded514 : Blocked 8 0 bank514 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded515 : Blocked 8 0 bank515 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded516 : Blocked 8 0 bank516 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded517 : Blocked 8 0 bank517 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded518 : Blocked 8 0 bank518 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded519 : Blocked 8 0 bank519 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded520 : Blocked 8 0 bank520 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded521 : Blocked 8 0 bank521 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded522 : Blocked 8 0 bank522 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded523 : Blocked 8 0 bank523 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded524 : Blocked 8 0 bank524 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded525 : Blocked 8 0 bank525 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded526 : Blocked 8 0 bank526 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded527 : Blocked 8 0 bank527 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded528 : Blocked 8 0 bank528 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded529 : Blocked 8 0 bank529 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded530 : Blocked 8 0 bank530 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded531 : Blocked 8 0 bank531 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded532 : Blocked 8 0 bank532 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded533 : Blocked 8 0 bank533 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded534 : Blocked 8 0 bank534 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded535 : Blocked 8 0 bank535 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded536 : Blocked 8 0 bank536 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded537 : Blocked 8 0 bank537 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded538 : Blocked 8 0 bank538 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded539 : Blocked 8 0 bank539 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded540 : Blocked 8 0 bank540 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded541 : Blocked 8 0 bank541 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded542 : Blocked 8 0 bank542 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded543 : Blocked 8 0 bank543 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded544 : Blocked 8 0 bank544 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded545 : Blocked 8 0 bank545 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded546 : Blocked 8 0 bank546 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded547 : Blocked 8 0 bank547 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded548 : Blocked 8 0 bank548 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded549 : Blocked 8 0 bank549 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded550 : Blocked 8 0 bank550 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded551 : Blocked 8 0 bank551 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded552 : Blocked 8 0 bank552 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded553 : Blocked 8 0 bank553 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded554 : Blocked 8 0 bank554 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded555 : Blocked 8 0 bank555 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded556 : Blocked 9 0 bank556 :=
  block_step [] [bank488, bank489, bank490, bank491, bank492, bank493, bank494, bank495, bank496, bank497, bank498, bank499, bank500, bank501, bank502, bank503, bank504, bank505, bank506, bank507, bank508, bank509, bank510, bank511, bank512, bank513, bank514, bank515, bank516, bank517, bank518, bank519, bank520, bank521, bank522, bank523, bank524, bank525, bank526, bank527, bank528, bank529, bank530, bank531, bank532, bank533, bank534, bank535, bank536, bank537, bank538, bank539, bank540, bank541, bank542, bank543, bank544, bank545, bank546, bank547, bank548, bank549, bank550, bank551, bank552, bank553, bank554, bank555]
    True.intro
    ⟨excluded488, excluded489, excluded490, excluded491, excluded492, excluded493, excluded494, excluded495, excluded496, excluded497, excluded498, excluded499, excluded500, excluded501, excluded502, excluded503, excluded504, excluded505, excluded506, excluded507, excluded508, excluded509, excluded510, excluded511, excluded512, excluded513, excluded514, excluded515, excluded516, excluded517, excluded518, excluded519, excluded520, excluded521, excluded522, excluded523, excluded524, excluded525, excluded526, excluded527, excluded528, excluded529, excluded530, excluded531, excluded532, excluded533, excluded534, excluded535, excluded536, excluded537, excluded538, excluded539, excluded540, excluded541, excluded542, excluded543, excluded544, excluded545, excluded546, excluded547, excluded548, excluded549, excluded550, excluded551, excluded552, excluded553, excluded554, excluded555, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded557 : Blocked 9 1 bank0 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded558 : Blocked 9 1 bank1 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded559 : Blocked 9 1 bank2 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded560 : Blocked 9 1 bank3 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded561 : Blocked 8 0 bank557 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded562 : Blocked 8 0 bank558 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded563 : Blocked 8 1 bank559 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded564 : Blocked 8 1 bank560 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded565 : Blocked 8 1 bank561 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded566 : Blocked 8 1 bank562 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded567 : Blocked 8 1 bank563 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded568 : Blocked 8 1 bank564 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded569 : Blocked 8 1 bank565 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded570 : Blocked 8 1 bank566 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded571 : Blocked 8 1 bank567 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded572 : Blocked 8 1 bank568 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded573 : Blocked 8 1 bank569 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded574 : Blocked 8 1 bank570 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded575 : Blocked 8 1 bank571 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded576 : Blocked 8 1 bank572 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded577 : Blocked 8 1 bank573 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded578 : Blocked 8 1 bank574 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded579 : Blocked 8 1 bank575 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded580 : Blocked 8 1 bank576 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded581 : Blocked 8 1 bank577 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded582 : Blocked 8 1 bank578 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded583 : Blocked 8 1 bank579 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded584 : Blocked 8 1 bank580 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded585 : Blocked 8 1 bank581 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded586 : Blocked 8 1 bank582 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded587 : Blocked 8 1 bank583 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded588 : Blocked 8 1 bank584 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded589 : Blocked 8 1 bank585 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded590 : Blocked 8 1 bank586 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded591 : Blocked 9 1 bank4 :=
  block_step [bank74, bank143, bank214, bank283, bank352, bank423, bank492, bank557, bank558] [bank559, bank560, bank561, bank562, bank563, bank564, bank565, bank566, bank567, bank568, bank569, bank570, bank571, bank572, bank573, bank574, bank575, bank576, bank577, bank578, bank579, bank580, bank581, bank582, bank583, bank584, bank585, bank586]
    ⟨excluded74, excluded143, excluded214, excluded283, excluded352, excluded423, excluded492, excluded561, excluded562, True.intro⟩
    ⟨excluded563, excluded564, excluded565, excluded566, excluded567, excluded568, excluded569, excluded570, excluded571, excluded572, excluded573, excluded574, excluded575, excluded576, excluded577, excluded578, excluded579, excluded580, excluded581, excluded582, excluded583, excluded584, excluded585, excluded586, excluded587, excluded588, excluded589, excluded590, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded592 : Blocked 9 1 bank5 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded593 : Blocked 9 1 bank6 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded594 : Blocked 9 1 bank7 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded595 : Blocked 8 0 bank587 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded596 : Blocked 8 0 bank588 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded597 : Blocked 8 1 bank589 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded598 : Blocked 8 1 bank590 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded599 : Blocked 8 1 bank591 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded600 : Blocked 8 1 bank592 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded601 : Blocked 8 1 bank593 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded602 : Blocked 8 1 bank594 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded603 : Blocked 8 1 bank595 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded604 : Blocked 8 1 bank596 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded605 : Blocked 8 1 bank597 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded606 : Blocked 8 1 bank598 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded607 : Blocked 8 1 bank599 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded608 : Blocked 8 1 bank600 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded609 : Blocked 8 1 bank601 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded610 : Blocked 8 1 bank602 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded611 : Blocked 8 1 bank603 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded612 : Blocked 8 1 bank604 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded613 : Blocked 8 1 bank605 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded614 : Blocked 8 1 bank606 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded615 : Blocked 8 1 bank607 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded616 : Blocked 8 1 bank608 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded617 : Blocked 8 1 bank609 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded618 : Blocked 8 1 bank610 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded619 : Blocked 8 1 bank611 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded620 : Blocked 8 1 bank612 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded621 : Blocked 8 1 bank613 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded622 : Blocked 9 1 bank8 :=
  block_step [bank78, bank147, bank218, bank287, bank356, bank427, bank496, bank587, bank588] [bank589, bank590, bank591, bank592, bank593, bank594, bank595, bank596, bank597, bank598, bank599, bank600, bank601, bank579, bank602, bank603, bank604, bank605, bank606, bank607, bank608, bank609, bank610, bank611, bank612, bank613]
    ⟨excluded78, excluded147, excluded218, excluded287, excluded356, excluded427, excluded496, excluded595, excluded596, True.intro⟩
    ⟨excluded597, excluded598, excluded599, excluded600, excluded601, excluded602, excluded603, excluded604, excluded605, excluded606, excluded607, excluded608, excluded609, excluded583, excluded610, excluded611, excluded612, excluded613, excluded614, excluded615, excluded616, excluded617, excluded618, excluded619, excluded620, excluded621, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded623 : Blocked 9 1 bank9 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded624 : Blocked 9 1 bank10 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded625 : Blocked 9 1 bank11 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded626 : Blocked 9 1 bank12 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded627 : Blocked 8 0 bank614 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded628 : Blocked 8 1 bank615 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded629 : Blocked 8 1 bank616 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded630 : Blocked 8 1 bank617 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded631 : Blocked 8 1 bank618 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded632 : Blocked 8 1 bank619 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded633 : Blocked 8 1 bank620 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded634 : Blocked 8 1 bank621 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded635 : Blocked 8 1 bank622 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded636 : Blocked 8 1 bank623 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded637 : Blocked 8 1 bank624 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded638 : Blocked 8 1 bank625 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded639 : Blocked 8 1 bank626 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded640 : Blocked 8 1 bank627 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded641 : Blocked 7 0 bank628 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded642 : Blocked 7 0 bank629 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded643 : Blocked 7 0 bank630 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded644 : Blocked 7 0 bank631 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded645 : Blocked 7 0 bank632 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded646 : Blocked 7 0 bank633 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded647 : Blocked 7 0 bank634 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded648 : Blocked 7 1 bank635 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded649 : Blocked 7 1 bank636 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded650 : Blocked 7 1 bank637 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded651 : Blocked 7 1 bank638 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded652 : Blocked 7 1 bank639 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded653 : Blocked 7 1 bank640 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded654 : Blocked 7 1 bank641 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded655 : Blocked 7 1 bank642 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded656 : Blocked 7 1 bank643 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded657 : Blocked 7 1 bank644 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded658 : Blocked 7 1 bank645 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded659 : Blocked 7 1 bank646 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded660 : Blocked 7 1 bank647 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded661 : Blocked 8 1 bank21 :=
  block_step [bank628, bank629, bank630, bank631, bank632, bank633, bank634] [bank635, bank636, bank637, bank638, bank639, bank640, bank641, bank642, bank643, bank644, bank645, bank646, bank647]
    ⟨excluded641, excluded642, excluded643, excluded644, excluded645, excluded646, excluded647, True.intro⟩
    ⟨excluded648, excluded649, excluded650, excluded651, excluded652, excluded653, excluded654, excluded655, excluded656, excluded657, excluded658, excluded659, excluded660, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded662 : Blocked 8 1 bank22 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded663 : Blocked 8 1 bank648 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded664 : Blocked 8 1 bank649 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded665 : Blocked 8 1 bank650 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded666 : Blocked 8 1 bank651 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded667 : Blocked 8 1 bank652 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded668 : Blocked 8 1 bank653 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded669 : Blocked 8 1 bank654 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded670 : Blocked 8 1 bank655 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded671 : Blocked 8 1 bank656 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded672 : Blocked 8 1 bank657 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded673 : Blocked 8 1 bank658 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded674 : Blocked 8 1 bank659 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded675 : Blocked 8 1 bank660 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded676 : Blocked 8 1 bank661 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded677 : Blocked 8 1 bank662 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded678 : Blocked 8 1 bank663 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded679 : Blocked 8 1 bank664 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded680 : Blocked 8 1 bank665 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded681 : Blocked 8 1 bank666 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded682 : Blocked 8 1 bank667 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded683 : Blocked 8 1 bank668 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded684 : Blocked 8 1 bank669 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded685 : Blocked 8 1 bank670 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded686 : Blocked 8 1 bank671 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded687 : Blocked 8 1 bank672 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded688 : Blocked 8 1 bank673 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded689 : Blocked 8 1 bank674 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded690 : Blocked 8 1 bank675 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded691 : Blocked 9 1 bank13 :=
  block_step [bank83, bank156, bank296, bank365, bank436, bank505, bank614] [bank615, bank616, bank617, bank562, bank618, bank619, bank620, bank592, bank621, bank622, bank623, bank624, bank625, bank626, bank627, bank21, bank22, bank648, bank649, bank650, bank651, bank652, bank653, bank654, bank655, bank656, bank657, bank658, bank659, bank660, bank661, bank662, bank663, bank664, bank665, bank666, bank667, bank668, bank669, bank670, bank671, bank672, bank673, bank674, bank675]
    ⟨excluded83, excluded156, excluded296, excluded365, excluded436, excluded505, excluded627, True.intro⟩
    ⟨excluded628, excluded629, excluded630, excluded566, excluded631, excluded632, excluded633, excluded600, excluded634, excluded635, excluded636, excluded637, excluded638, excluded639, excluded640, excluded661, excluded662, excluded663, excluded664, excluded665, excluded666, excluded667, excluded668, excluded669, excluded670, excluded671, excluded672, excluded673, excluded674, excluded675, excluded676, excluded677, excluded678, excluded679, excluded680, excluded681, excluded682, excluded683, excluded684, excluded685, excluded686, excluded687, excluded688, excluded689, excluded690, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded692 : Blocked 9 1 bank14 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded693 : Blocked 9 1 bank15 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded694 : Blocked 9 1 bank16 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded695 : Blocked 8 0 bank676 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded696 : Blocked 7 0 bank677 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded697 : Blocked 7 0 bank678 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded698 : Blocked 7 0 bank679 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded699 : Blocked 7 0 bank680 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded700 : Blocked 7 0 bank681 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded701 : Blocked 7 0 bank682 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded702 : Blocked 7 0 bank683 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded703 : Blocked 7 0 bank684 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded704 : Blocked 7 0 bank685 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded705 : Blocked 7 0 bank686 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded706 : Blocked 7 0 bank687 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded707 : Blocked 7 0 bank688 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded708 : Blocked 8 0 bank689 :=
  block_step [] [bank677, bank678, bank634, bank679, bank680, bank681, bank682, bank683, bank684, bank685, bank686, bank687, bank688]
    True.intro
    ⟨excluded696, excluded697, excluded647, excluded698, excluded699, excluded700, excluded701, excluded702, excluded703, excluded704, excluded705, excluded706, excluded707, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded709 : Blocked 8 1 bank17 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded710 : Blocked 8 1 bank18 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded711 : Blocked 8 1 bank19 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded712 : Blocked 8 1 bank20 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded713 : Blocked 8 1 bank23 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded714 : Blocked 8 1 bank690 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded715 : Blocked 8 1 bank691 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded716 : Blocked 8 1 bank24 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded717 : Blocked 8 1 bank25 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded718 : Blocked 8 1 bank26 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded719 : Blocked 8 1 bank27 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded720 : Blocked 7 0 bank692 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded721 : Blocked 7 0 bank693 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded722 : Blocked 7 0 bank694 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded723 : Blocked 7 0 bank695 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded724 : Blocked 7 0 bank696 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded725 : Blocked 7 0 bank697 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded726 : Blocked 7 1 bank698 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded727 : Blocked 7 1 bank699 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded728 : Blocked 7 1 bank700 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded729 : Blocked 7 1 bank701 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded730 : Blocked 7 1 bank702 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded731 : Blocked 7 1 bank703 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded732 : Blocked 7 1 bank704 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded733 : Blocked 7 1 bank705 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded734 : Blocked 7 1 bank706 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded735 : Blocked 7 1 bank707 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded736 : Blocked 7 1 bank708 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded737 : Blocked 7 1 bank709 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded738 : Blocked 8 1 bank28 :=
  block_step [bank692, bank693, bank694, bank695, bank696, bank682, bank697] [bank698, bank699, bank700, bank638, bank701, bank702, bank703, bank704, bank705, bank706, bank707, bank708, bank709]
    ⟨excluded720, excluded721, excluded722, excluded723, excluded724, excluded701, excluded725, True.intro⟩
    ⟨excluded726, excluded727, excluded728, excluded651, excluded729, excluded730, excluded731, excluded732, excluded733, excluded734, excluded735, excluded736, excluded737, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded739 : Blocked 8 1 bank29 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded740 : Blocked 8 1 bank30 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded741 : Blocked 8 1 bank31 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded742 : Blocked 8 1 bank32 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded743 : Blocked 8 1 bank33 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded744 : Blocked 8 1 bank34 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded745 : Blocked 8 1 bank35 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded746 : Blocked 8 1 bank36 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded747 : Blocked 8 1 bank37 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded748 : Blocked 8 1 bank38 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded749 : Blocked 8 1 bank39 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded750 : Blocked 8 1 bank40 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded751 : Blocked 8 1 bank41 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded752 : Blocked 9 1 bank42 :=
  block_step [bank87, bank160, bank231, bank300, bank369, bank440, bank509, bank676, bank689] [bank17, bank18, bank19, bank20, bank21, bank22, bank23, bank690, bank691, bank24, bank25, bank26, bank27, bank28, bank29, bank30, bank31, bank32, bank33, bank34, bank35, bank36, bank37, bank38, bank39, bank40, bank41]
    ⟨excluded87, excluded160, excluded231, excluded300, excluded369, excluded440, excluded509, excluded695, excluded708, True.intro⟩
    ⟨excluded709, excluded710, excluded711, excluded712, excluded661, excluded662, excluded713, excluded714, excluded715, excluded716, excluded717, excluded718, excluded719, excluded738, excluded739, excluded740, excluded741, excluded742, excluded743, excluded744, excluded745, excluded746, excluded747, excluded748, excluded749, excluded750, excluded751, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded753 : Blocked 9 1 bank43 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded754 : Blocked 9 1 bank44 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded755 : Blocked 9 1 bank45 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded756 : Blocked 9 1 bank46 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded757 : Blocked 9 1 bank47 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded758 : Blocked 9 1 bank48 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded759 : Blocked 9 1 bank49 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded760 : Blocked 9 1 bank50 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded761 : Blocked 9 1 bank51 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded762 : Blocked 8 0 bank710 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded763 : Blocked 8 0 bank711 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded764 : Blocked 8 1 bank712 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded765 : Blocked 8 1 bank713 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded766 : Blocked 8 1 bank714 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded767 : Blocked 8 1 bank715 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded768 : Blocked 8 1 bank716 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded769 : Blocked 8 1 bank717 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded770 : Blocked 8 1 bank718 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded771 : Blocked 8 1 bank719 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded772 : Blocked 8 1 bank720 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded773 : Blocked 8 1 bank721 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded774 : Blocked 8 1 bank722 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded775 : Blocked 8 1 bank723 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded776 : Blocked 8 1 bank724 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded777 : Blocked 8 1 bank725 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded778 : Blocked 8 1 bank726 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded779 : Blocked 8 1 bank727 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded780 : Blocked 8 1 bank728 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded781 : Blocked 8 1 bank729 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded782 : Blocked 8 1 bank730 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded783 : Blocked 8 1 bank731 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded784 : Blocked 8 1 bank732 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded785 : Blocked 8 1 bank733 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded786 : Blocked 8 1 bank734 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded787 : Blocked 8 1 bank735 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded788 : Blocked 8 1 bank736 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded789 : Blocked 8 1 bank737 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded790 : Blocked 8 1 bank738 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded791 : Blocked 9 1 bank52 :=
  block_step [bank101, bank170, bank245, bank314, bank383, bank454, bank523, bank710, bank711] [bank597, bank712, bank713, bank714, bank715, bank716, bank717, bank718, bank719, bank720, bank721, bank722, bank723, bank724, bank725, bank726, bank727, bank728, bank729, bank730, bank731, bank732, bank733, bank734, bank735, bank736, bank737, bank738]
    ⟨excluded101, excluded170, excluded245, excluded314, excluded383, excluded454, excluded523, excluded762, excluded763, True.intro⟩
    ⟨excluded605, excluded764, excluded765, excluded766, excluded767, excluded768, excluded769, excluded770, excluded771, excluded772, excluded773, excluded774, excluded775, excluded776, excluded777, excluded778, excluded779, excluded780, excluded781, excluded782, excluded783, excluded784, excluded785, excluded786, excluded787, excluded788, excluded789, excluded790, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded792 : Blocked 9 1 bank53 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded793 : Blocked 8 0 bank739 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded794 : Blocked 8 0 bank740 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded795 : Blocked 8 1 bank741 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded796 : Blocked 8 1 bank742 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded797 : Blocked 8 1 bank743 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded798 : Blocked 8 1 bank744 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded799 : Blocked 8 1 bank745 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded800 : Blocked 8 1 bank746 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded801 : Blocked 8 1 bank747 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded802 : Blocked 8 1 bank748 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded803 : Blocked 8 1 bank749 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded804 : Blocked 8 1 bank750 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded805 : Blocked 8 1 bank751 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded806 : Blocked 8 1 bank752 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded807 : Blocked 8 1 bank753 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded808 : Blocked 8 1 bank754 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded809 : Blocked 8 1 bank755 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded810 : Blocked 8 1 bank756 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded811 : Blocked 8 1 bank757 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded812 : Blocked 8 1 bank758 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded813 : Blocked 8 1 bank759 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded814 : Blocked 8 1 bank760 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded815 : Blocked 8 1 bank761 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded816 : Blocked 8 1 bank762 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded817 : Blocked 8 1 bank763 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded818 : Blocked 8 1 bank764 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded819 : Blocked 9 1 bank54 :=
  block_step [bank103, bank172, bank247, bank316, bank385, bank456, bank525, bank739, bank740] [bank741, bank742, bank743, bank744, bank745, bank746, bank747, bank748, bank749, bank750, bank724, bank751, bank752, bank753, bank754, bank755, bank756, bank757, bank758, bank759, bank760, bank761, bank735, bank762, bank763, bank764]
    ⟨excluded103, excluded172, excluded247, excluded316, excluded385, excluded456, excluded525, excluded793, excluded794, True.intro⟩
    ⟨excluded795, excluded796, excluded797, excluded798, excluded799, excluded800, excluded801, excluded802, excluded803, excluded804, excluded776, excluded805, excluded806, excluded807, excluded808, excluded809, excluded810, excluded811, excluded812, excluded813, excluded814, excluded815, excluded787, excluded816, excluded817, excluded818, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded820 : Blocked 9 1 bank55 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded821 : Blocked 9 1 bank56 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded822 : Blocked 8 0 bank765 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded823 : Blocked 8 1 bank766 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded824 : Blocked 8 1 bank767 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded825 : Blocked 8 1 bank768 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded826 : Blocked 8 1 bank769 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded827 : Blocked 8 1 bank770 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded828 : Blocked 8 1 bank771 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded829 : Blocked 8 1 bank772 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded830 : Blocked 8 1 bank773 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded831 : Blocked 8 1 bank774 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded832 : Blocked 8 1 bank775 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded833 : Blocked 8 1 bank776 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded834 : Blocked 8 1 bank777 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded835 : Blocked 8 1 bank778 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded836 : Blocked 8 1 bank779 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded837 : Blocked 8 1 bank780 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded838 : Blocked 8 1 bank781 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded839 : Blocked 8 1 bank782 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded840 : Blocked 8 1 bank783 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded841 : Blocked 8 1 bank784 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded842 : Blocked 8 1 bank785 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded843 : Blocked 8 1 bank786 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded844 : Blocked 8 1 bank787 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded845 : Blocked 8 1 bank788 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded846 : Blocked 8 1 bank789 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded847 : Blocked 8 1 bank790 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded848 : Blocked 8 1 bank791 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded849 : Blocked 8 1 bank792 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded850 : Blocked 8 1 bank793 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded851 : Blocked 8 1 bank794 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded852 : Blocked 8 1 bank795 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded853 : Blocked 8 1 bank796 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded854 : Blocked 8 1 bank797 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded855 : Blocked 8 1 bank798 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded856 : Blocked 8 1 bank799 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded857 : Blocked 8 1 bank800 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded858 : Blocked 8 1 bank801 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded859 : Blocked 8 1 bank802 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded860 : Blocked 8 1 bank803 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded861 : Blocked 8 1 bank804 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded862 : Blocked 9 1 bank57 :=
  block_step [bank110, bank181, bank250, bank392, bank463, bank532, bank765] [bank766, bank767, bank768, bank769, bank770, bank771, bank772, bank601, bank773, bank774, bank775, bank776, bank777, bank778, bank656, bank779, bank28, bank30, bank780, bank781, bank782, bank783, bank784, bank785, bank786, bank787, bank788, bank725, bank789, bank753, bank790, bank791, bank792, bank793, bank794, bank795, bank796, bank797, bank798, bank799, bank800, bank801, bank802, bank803, bank804]
    ⟨excluded110, excluded181, excluded250, excluded392, excluded463, excluded532, excluded822, True.intro⟩
    ⟨excluded823, excluded824, excluded825, excluded826, excluded827, excluded828, excluded829, excluded609, excluded830, excluded831, excluded832, excluded833, excluded834, excluded835, excluded671, excluded836, excluded738, excluded740, excluded837, excluded838, excluded839, excluded840, excluded841, excluded842, excluded843, excluded844, excluded845, excluded777, excluded846, excluded807, excluded847, excluded848, excluded849, excluded850, excluded851, excluded852, excluded853, excluded854, excluded855, excluded856, excluded857, excluded858, excluded859, excluded860, excluded861, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded863 : Blocked 9 1 bank58 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded864 : Blocked 9 1 bank59 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded865 : Blocked 9 1 bank60 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded866 : Blocked 8 0 bank805 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded867 : Blocked 8 0 bank806 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded868 : Blocked 8 1 bank807 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded869 : Blocked 8 1 bank808 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded870 : Blocked 8 1 bank809 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded871 : Blocked 8 1 bank810 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded872 : Blocked 8 1 bank811 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded873 : Blocked 8 1 bank812 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded874 : Blocked 8 1 bank813 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded875 : Blocked 8 1 bank814 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded876 : Blocked 8 1 bank815 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded877 : Blocked 8 1 bank816 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded878 : Blocked 8 1 bank817 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded879 : Blocked 8 1 bank818 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded880 : Blocked 8 1 bank819 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded881 : Blocked 8 1 bank820 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded882 : Blocked 8 1 bank821 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded883 : Blocked 8 1 bank822 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded884 : Blocked 8 1 bank823 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded885 : Blocked 8 1 bank824 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded886 : Blocked 8 1 bank825 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded887 : Blocked 8 1 bank826 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded888 : Blocked 8 1 bank827 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded889 : Blocked 8 1 bank828 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded890 : Blocked 9 1 bank61 :=
  block_step [bank114, bank185, bank254, bank327, bank396, bank467, bank536, bank805, bank806] [bank574, bank583, bank807, bank808, bank809, bank660, bank810, bank811, bank812, bank813, bank754, bank814, bank815, bank816, bank817, bank818, bank819, bank820, bank821, bank822, bank823, bank824, bank825, bank826, bank827, bank828]
    ⟨excluded114, excluded185, excluded254, excluded327, excluded396, excluded467, excluded536, excluded866, excluded867, True.intro⟩
    ⟨excluded578, excluded587, excluded868, excluded869, excluded870, excluded675, excluded871, excluded872, excluded873, excluded874, excluded808, excluded875, excluded876, excluded877, excluded878, excluded879, excluded880, excluded881, excluded882, excluded883, excluded884, excluded885, excluded886, excluded887, excluded888, excluded889, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded891 : Blocked 9 1 bank62 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded892 : Blocked 9 1 bank63 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded893 : Blocked 9 1 bank64 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded894 : Blocked 9 1 bank65 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded895 : Blocked 9 1 bank66 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded896 : Blocked 9 1 bank67 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded897 : Blocked 9 1 bank68 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded898 : Blocked 10 1 bank69 :=
  block_step [bank138, bank209, bank278, bank347, bank418, bank487, bank556] [bank0, bank1, bank2, bank3, bank4, bank5, bank6, bank7, bank8, bank9, bank10, bank11, bank12, bank13, bank14, bank15, bank16, bank42, bank43, bank44, bank45, bank46, bank47, bank48, bank49, bank50, bank51, bank52, bank53, bank54, bank55, bank56, bank57, bank58, bank59, bank60, bank61, bank62, bank63, bank64, bank65, bank66, bank67, bank68]
    ⟨excluded138, excluded209, excluded278, excluded347, excluded418, excluded487, excluded556, True.intro⟩
    ⟨excluded557, excluded558, excluded559, excluded560, excluded591, excluded592, excluded593, excluded594, excluded622, excluded623, excluded624, excluded625, excluded626, excluded691, excluded692, excluded693, excluded694, excluded752, excluded753, excluded754, excluded755, excluded756, excluded757, excluded758, excluded759, excluded760, excluded761, excluded791, excluded792, excluded819, excluded820, excluded821, excluded862, excluded863, excluded864, excluded865, excluded890, excluded891, excluded892, excluded893, excluded894, excluded895, excluded896, excluded897, True.intro⟩
    (by decide +kernel) (by decide +kernel)

theorem zero_excluded : Blocked 9 0 root := excluded69

theorem one_excluded : Blocked 10 1 root := excluded898

end PEqualNP.Outside.L_meta_10854_aux

open PEqualNP.Outside.L_meta_10854_aux


theorem PEqualNP.Outside.L_meta_10854 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o basis single computes
  by_cases used : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · exact ⟨replacement.gates, replacement.output, replacement_basis,
      lower_with_not gates o basis single used computes zero_excluded one_excluded, replacement_correct⟩
  · refine ⟨gates, o, ?_, le_rfl, computes⟩
    intro g hg
    refine ⟨?_, (basis g hg).2⟩
    rcases (basis g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (used ⟨g, hg, h⟩).elim
