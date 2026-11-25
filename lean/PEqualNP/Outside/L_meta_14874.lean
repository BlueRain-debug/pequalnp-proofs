import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Fintype.Pi
import PEqualNP.Defs

-- Adapted from D Lam's L-meta-10852, following Vkuparin, ljste and jfsantoropereira.
namespace PEqualNP.Outside.L_meta_14874_aux

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


def evalT (T : ℕ) (x : Fin 8 → Bool) := Nat.testBit T (∑ i : Fin 8, if x i then 2 ^ (i : ℕ) else 0)
def sample (raw : List Sig) (s : Bool) (i : Fin 256) (j : Fin 8) := bit s i (raw.getD j.val zero)
private lemma sample_list (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 8 => raw.getD j.val zero) = raw) (s i) : List.ofFn (sample raw s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 8 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (T : ℕ) (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 8 => raw.getD j.val zero) = raw)
    (sample_ok : ∀ s i, evalT T (sample raw s i) = s) (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = evalT T x) : target ∈ execute C.gates raw := by
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
  (0x3aaabfffffffd555555555555555aaaaaaaaaaaaaaaaaab5556aaad555ffff61,0x2aaa9555555555555552800002aaaaaaa940000155555554a00000aaaaaaaa60),
  (0xccccd9999999e666666666666666cccccccccccccf3cccd999b3336666aaaa82,0x8cccd9999999e666666002aaab333333300155559999999800aaaacccccccc80),
  (0xf0f1e1e1e1e7878787878787878f0f0f0f0f0f0f3cf0f1e1e3c3c7878cccc04,0xf0f1e1e1e1e07878780033333c3c3c3c0019999e1e1e1e000ccccf0f0f0f000),
  (0xff01fe01fe07f807f807f807f80ff00ff00ff00fc0ff01fe03fc07f80f0f008,0xff01fe01fe07807f80303c3c3fc03fc0181e1e1fe01fe00c0f0f0ff00ff0000),
  (0xf0001fffe0007fff80007fff8000ffff0000ffff000fffe0003fff8000ff0010,0xf0001fffe0007ff800002bfc03fffc000015fe01fffe00000aff00ffff000000),
  (0x1fffffffffffffff80000000ffffffff0000000fffffffc0000000ffff21,0xaaaaaaa8000000033fffc0000000019fffe000000000cffff0000000001),
  (0xffffe00000007fffffffffffffff000000000000000fffffffffffffff00004e,0x500020000000000000043c0000000000021e0000000000010f0000000000000e),
  (0x7ffffffffffffffffffffffffffffff000000000000000000090,0x7c0000000000003e0000000000001f000000000000010)]

def goalTable : Nat := 0xfffffffffffffffefffffffffffffcfcfffefffefffefffeaaaaaaaa00000000

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

def edgeFn (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < ([0, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)

def replacement : Circuit :=
  ⟨[⟨.or,[1,2]⟩, ⟨.or,[0,3]⟩, ⟨.or,[8,9]⟩,
    ⟨.and,[6,10]⟩, ⟨.or,[4,5]⟩, ⟨.or,[8,12]⟩,
    ⟨.and,[7,13]⟩, ⟨.and,[0,5]⟩, ⟨.or,[11,14]⟩,
    ⟨.or,[16,15]⟩], 17⟩

theorem replacement_size : replacement.gates.length = 10 := rfl

theorem replacement_basis : ∀ g ∈ replacement.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [replacement]

set_option maxRecDepth 16000 in
theorem replacement_correct : ∀ x : Fin 8 → Bool, replacement.eval (List.ofFn x) = edgeFn x := by
  decide +kernel

theorem table_agrees : ∀ x : Fin 8 → Bool, edgeFn x = evalT goalTable x := by
  decide +kernel

theorem lower_with_not (gs : List Gate) (o : ℕ)
    (basis : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (oneNot : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (used : ∃ g ∈ gs, g.op = .not)
    (correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = edgeFn x)
    (zeroNot : Blocked 8 0 root) (one : Blocked 9 1 root) : 10 ≤ gs.length := by
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



def sig3 : Sig := (0x3aaabfffffffd555555555555555aaaaaaaaaaaaaaaaaab5556aaad555ffff61, 0x2aaa9555555555555552800002aaaaaaa940000155555554a00000aaaaaaaa60)

def sig4 : Sig := (0xccccd9999999e666666666666666cccccccccccccf3cccd999b3336666aaaa82, 0x8cccd9999999e666666002aaab333333300155559999999800aaaacccccccc80)

def sig5 : Sig := (0xf0f1e1e1e1e7878787878787878f0f0f0f0f0f0f3cf0f1e1e3c3c7878cccc04, 0xf0f1e1e1e1e07878780033333c3c3c3c0019999e1e1e1e000ccccf0f0f0f000)

def sig6 : Sig := (0xff01fe01fe07f807f807f807f80ff00ff00ff00fc0ff01fe03fc07f80f0f008, 0xff01fe01fe07807f80303c3c3fc03fc0181e1e1fe01fe00c0f0f0ff00ff0000)

def sig7 : Sig := (0xf0001fffe0007fff80007fff8000ffff0000ffff000fffe0003fff8000ff0010, 0xf0001fffe0007ff800002bfc03fffc000015fe01fffe00000aff00ffff000000)

def sig8 : Sig := (0x1fffffffffffffff80000000ffffffff0000000fffffffc0000000ffff21, 0xaaaaaaa8000000033fffc0000000019fffe000000000cffff0000000001)

def sig9 : Sig := (0xffffe00000007fffffffffffffff000000000000000fffffffffffffff00004e, 0x500020000000000000043c0000000000021e0000000000010f0000000000000e)

def sig10 : Sig := (0x7ffffffffffffffffffffffffffffff000000000000000000090, 0x7c0000000000003e0000000000001f000000000000010)

def sig12 : Sig := (0xfeeefffffffff777777777777777eeeeeeeeeeeeefbeeefdddfbbbf777ffffe3, 0xaeeeddddddddf777777282aaabbbbbbbb9415555dddddddca0aaaaeeeeeeeee0)

def sig14 : Sig := (0x3fafbffffffffd7d7d7d7d7d7d7dfafafafafafafbefafbf5f7ebefd7dffff65, 0x2faf9f5f5f5f57d7d7d2833333ebebebe9419999f5f5f5f4a0ccccfafafafa60)

def sig16 : Sig := (0x3ffabfffffffffd57fd57fd57fd5ffaaffaaffaafeaffabff57feaffd5ffff69, 0x2ffa9ff55ff57d57fd5383c3c3feabfea9c1e1e1ff55ff54e0f0f0ffaaffaa60)

def sig18 : Sig := (0xfaaabfffffffffffd5557fffd555ffffaaaaffffaaaffff5557fffd555ffff71, 0xfaaa9ffff5557ffd5552abfc03fffeaaa955fe01ffff5554aaff00ffffaaaa60)

def sig19 : Sig := (0x1fffffffd555555500000000aaaaaaaa0000000aaab55540000000ffff21, 0x0)

def sig24 : Sig := (0x3aaabffffffffffffffffffffffffffffffffffffffaaab5556aaad555fffff1, 0x2aaa9555555555555557c00002aaaaaaabe0000155555555f00000aaaaaaaa70)

def sig26 : Sig := (0xfff1ffe1ffe7ff87ff87ff87ff8fff0fff0fff0ffcfff1ffe3ffc7ff8fcfc0c, 0xfff1ffe1ffe7f87ff8303f3f3ffc3ffc181f9f9ffe1ffe0c0fcfcfff0fff000)

def sig28 : Sig := (0x3fffbffffffffffd7ffd7ffd7ffdfffafffafffaffefffbfff7ffefffdffff6d, 0x2fff9fff5fff7fd7ffd383f3f3ffebffe9c1f9f9fff5fff4e0fcfcfffafffa60)

def sig30 : Sig := (0xf0001fffffffffffffffffff8000ffffffffffff000fffffffffff8000ffff31, 0xf0001fffeaaafff800003bfffffffc00001dfffffffe00000effffffff000001)

def sig32 : Sig := (0xffffffffe0007fffffffffffffffffff0000ffff000fffffffffffffffff005e, 0xf0003fffe0007ff800043ffc03fffc00021ffe01fffe00010fff00ffff00000e)

def sig33 : Sig := (0x7fff80007fff8000ffff0000ffff000000000000000000000010, 0x0)

def sig34 : Sig := (0xf0001fffe0007fffffffffffffffffffffffffffffffffe0003fff8000ff0090, 0xf0001fffe0007ff80007ebfc03fffc0003f5fe01fffe0001faff00ffff000010)

def sig38 : Sig := (0xffff1ffffffe7ffffff87ffffff8fffffff0ffffffcffffffe3ffffff8fffc1c, 0xffff1ffffffe7fffff832bfff3ffffffc195fff9ffffffe0cafffcfffffff000)

def sig42 : Sig := (0xffffffffffffffffffffffffffffffffffff0000000fffffffffffffffffff6f, 0x50002aaaaaaa800000043ffffc000000021ffffe000000010fffff000000000f)

def sig44 : Sig := (0x1fffffffffffffffffffffffffffffffffffffffffffffc0000000ffffb1, 0xaaaaaaa80000007f3fffc00000003f9fffe00000001fcffff0000000011)

def sig50 : Sig := (0xffffe00000007fffffffffffffffffffffffffffffffffffffffffffff0000de, 0x50002000000000000007fc000000000003fe000000000001ff0000000000001e)

def sig62 : Sig := (0xfff1ffffffffffffffffff87ff8fffffffffff0ffcffffffffffc7ff8ffff2d, 0xfff1ffebffeff87ff8333ffffffc3ffc199ffffffe1ffe0ccfffffff0fff001)

def sig65 : Sig := (0xf000000000007fff80007fff8000ffff0000ffff000fffe0003fff8000000010, 0x5000000000000000000028000000000000140000000000000a00000000000000)

def sig68 : Sig := (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x50002aaaaaaa80000007fffffc00000003fffffe00000001ffffff000000001f)

def sig80 : Sig := (0xfff000000007ff87ff87ff87ff8000000000000000fff1ffe3ffc7ff800000c, 0x0)

def sig83 : Sig := (0xfff1ffe1ffe7fffffffffffffffffffffffffffffffff1ffe3ffc7ff8fcfc9c, 0xfff1ffe1ffe7f87ff87c3f3f3ffc3ffc3e1f9f9ffe1ffe1f0fcfcfff0fff010)

def sig101 : Sig := (0xff0f1ffffe1e7ffff8787ffff878fffff0f0fffff3cffffe1e3ffff878ffcc14, 0xff0f1ffffe1e7fff87802bff33ffffc3c015ff99ffffe1e00affccfffff0f000)

def sig105 : Sig := (0xff01fffffffffffffffff807f80ffffffffff00fc0fffffffffc07f80ffff29, 0xff01feabfeaf807f80333fffffc03fc0199fffffe01fe00ccffffff00ff0001)

def sig106 : Sig := (0xff0000000007f807f807f807f80000000000000000ff01fe03fc07f80000008, 0x0)

def sig109 : Sig := (0xff01fe01fe07ffffffffffffffffffffffffffffffff01fe03fc07f80f0f098, 0xff01fe01fe07807f807c3c3c3fc03fc03e1e1e1fe01fe01f0f0f0ff00ff0010)

def sig111 : Sig := (0xfffefffffffffff77ff77ff77ff7ffeeffeeffeeffbffefffdfffbfff7ffffeb, 0xaffedffddffdff77ff7383ebebffbbffb9c1f5f5ffddffdce0fafaffeeffeee0)

def sig129 : Sig := (0xf0f1ffffffffffffffff8787878fffffffff0f0f3cffffffffc3c7878ffff25, 0xf0f1ebebebe8787878033ffffc3c3c3c019ffffe1e1e1e00cfffff0f0f0f001)

def sig130 : Sig := (0xf0f000000007878787878787878000000000000000f0f1e1e3c3c7878000004, 0x0)

def sig133 : Sig := (0xf0f1e1e1e1e7fffffffffffffffffffffffffffffff0f1e1e3c3c7878cccc94, 0xf0f1e1e1e1e07878787c33333c3c3c3c3e19999e1e1e1e1f0ccccf0f0f0f010)

def sig135 : Sig := (0xffefffffffffff7f7f7f7f7f7f7ffefefefefefeffffefffdfffbfff7fffffe7, 0xafefdfdfdfdff7f7f7f283bbbbfbfbfbf941ddddfdfdfdfca0eeeefefefefee0)

def sig137 : Sig := (0xfff01fffffe07fffff807fffff80ffffff00fffffc0fffffe03fffff80fff018, 0xfff01fffffe07ffff8032bffc3fffffc0195ffe1fffffe00cafff0ffffff0000)

def sig139 : Sig := (0xfffabfffffffffffffd57fffffd5ffffffaafffffeaffffff57fffffd5ffff79, 0xfffa9ffffff57ffffd53abffc3fffffea9d5ffe1ffffff54eafff0ffffffaa60)

def sig143 : Sig := (0xfff01fffffffffffffffffffff80fffffffffffffc0fffffffffffff80ffff39, 0xfff01fffffeafffff8033bfffffffffc019dfffffffffe00ceffffffffff0001)

def sig156 : Sig := (0xfff01fffffe07fffffffffffffffffffffffffffffffffffe03fffff80fff098, 0xfff01fffffe07ffff807ebffc3fffffc03f5ffe1fffffe01fafff0ffffff0010)

def sig159 : Sig := (0xff0000000007f807f807f807f80ff00ff00ff00fc0ff01fe03fc07f80000008, 0x30000000000000180000000000000c000000000000000)

def sig162 : Sig := (0xf0f000000007878787878787878f0f0f0f0f0f0f3cf0f1e1e3c3c7878000004, 0x0)

def sig171 : Sig := (0xcffcdff99ff9ffe67fe67fe67fe6ffccffccffccff3ffcdff9bff37fe6fafa8a, 0x8ffcdff99ff9fe67fe6303ebebff33ff3181f5f5ff99ff98c0fafaffccffcc80)

def sig177 : Sig := (0xcffcdfffffffffffffffffe67fe6ffffffffffccff3ffffffffff37fe6ffffab, 0x8ffcdffbbffbfe67fe6333ffffff33ff3199ffffff99ff98ccffffffccffcc81)

def sig180 : Sig := (0xcffcc00000007fe67fe67fe67fe6000000000000000ffcdff9bff37fe600000a, 0x0)

def sig184 : Sig := (0x7fe67fe67fe67fe6ffccffccffccff3000000000000000000080, 0x30000000000000180000000000000c000000000000000)

def sig185 : Sig := (0xcffcdff99ff9fffffffffffffffffffffffffffffffffcdff9bff37fe6fafa9a, 0x8ffcdff99ff9fe67fe67c3ebebff33ff33e1f5f5ff99ff99f0fafaffccffcc90)

def sig188 : Sig := (0xfffcdffffff9ffffffe67fffffe6ffffffccffffff3ffffff9bfffffe6fffa9a, 0xfffcdffffff9fffffe632bffebffffff3195fff5ffffff98cafffaffffffcc80)

def sig201 : Sig := (0xfcccdffff999ffffe6667fffe666ffffccccffffcf3ffff999bfffe666ffaa92, 0xfcccdffff999fffe66602bfeabffff333015ff55ffff99980affaaffffcccc80)

def sig203 : Sig := (0xccccdfffffffffffffffe6666666ffffffffcccccf3ffffffff3336666ffffa3, 0x8cccdbbbbbbbe666666033ffff3333333019ffff999999980cffffcccccccc81)

def sig204 : Sig := (0xccccc00000006666666666666666000000000000000cccd999b3336666000002, 0x0)

def sig206 : Sig := (0x6666666666666666cccccccccccccf3000000000000000000080, 0x0)

def sig207 : Sig := (0xccccd9999999fffffffffffffffffffffffffffffffcccd999b3336666aaaa92, 0x8cccd9999999e6666667c2aaab33333333e1555599999999f0aaaacccccccc90)

def sig210 : Sig := (0xccccc00000006666666666666666cccccccccccccf3cccd999b3336666000082, 0x0)

def sig234 : Sig := (0xcfcfdf9f9f9ffe7e7e7e7e7e7e7efcfcfcfcfcfcffffcfdf9fbf3f7e7eeeee86, 0x8fcfdf9f9f9fe7e7e7e003bbbbf3f3f3f001ddddf9f9f9f800eeeefcfcfcfc80)

def sig240 : Sig := (0xcfcfdffffffffffffffffe7e7e7efffffffffcfcffffffffffff3f7e7effffa7, 0x8fcfdfbfbfbfe7e7e7e033fffff3f3f3f019fffff9f9f9f80cfffffcfcfcfc81)

def sig248 : Sig := (0xcfcfc00000007e7e7e7e7e7e7e7e000000000000000fcfdf9fbf3f7e7e000006, 0x0)

def sig252 : Sig := (0x7e7e7e7e7e7e7e7efcfcfcfcfcfcfff000000000000000000080, 0x0)

def sig253 : Sig := (0xcfcfdf9f9f9fffffffffffffffffffffffffffffffffcfdf9fbf3f7e7eeeee96, 0x8fcfdf9f9f9fe7e7e7e7c3bbbbf3f3f3f3e1ddddf9f9f9f9f0eeeefcfcfcfc90)

def sig255 : Sig := (0xffcfdfffff9ffffffe7e7ffffe7efffffcfcffffffffffff9fbffffe7effee96, 0xffcfdfffff9fffffe7e02bffbbfffff3f015ffddfffff9f80affeefffffcfc80)

def sig273 : Sig := (0xcfffdfff9ffffffe7ffe7ffe7ffefffcfffcfffcffffffdfffbfff7ffefefe8e, 0x8fffdfff9fffffe7ffe303fbfbfff3fff181fdfdfff9fff8c0fefefffcfffc80)

def sig461 : Sig := (0xffffe00000007fffffffffffffffffff0000ffff000fffffffffffffff00005e, 0x500020000000000000043c0000000000021e0000000000010f0000000000000e)

def sig465 : Sig := (0x3aaabfffffffffffd5557fffd555ffffaaaaffffaaaaaab5556aaad555ffff71, 0x2aaa9555555555555552800002aaaaaaa940000155555554a00000aaaaaaaa60)

def sig474 : Sig := (0x1fffffffffffffffffff8000ffffffffffff000fffffffc0000000ffff31, 0xaaaaaaa8000000033fffc0000000019fffe000000000cffff0000000001)

def sig551 : Sig := (0xff01fe01fe07fffff807fffff80ffffff00fffffc0ff01fe03fc07f80f0f018, 0xff01fe01fe07807f80303c3c3fc03fc0181e1e1fe01fe00c0f0f0ff00ff0000)

def sig758 : Sig := (0xf0f1e1e1e1e7ffff8787ffff878fffff0f0fffff3cf0f1e1e3c3c7878cccc14, 0xf0f1e1e1e1e07878780033333c3c3c3c0019999e1e1e1e000ccccf0f0f0f000)

def sig995 : Sig := (0xccccd9999999ffffe6667fffe666ffffccccffffcf3cccd999b3336666aaaa92, 0x8cccd9999999e666666002aaab333333300155559999999800aaaacccccccc80)

def sig1299 : Sig := (0xc555400000002aaaaaaaaaaaaaaa5555555555555555554aaa95552aaa00009e, 0xd5556aaaaaaaaaaaaaad7ffffd55555556bffffeaaaaaaab5fffff555555559f)

def sig1301 : Sig := (0xc5555fffffffffffffffaaaaaaaaffffffff5555555fffffffd5552aaaffffbf, 0xd5556aaaaaaaaaaaaaad7ffffd55555556bffffeaaaaaaab5fffff555555559f)

def sig1311 : Sig := (0x2aaaaaaaaaaaaaaa555555555555555000000000000000000090, 0x540000000000002a00000000000015000000000000010)

def sig1316 : Sig := (0xc000000000002aaa80002aaa8000555500005555000555400015550000000010, 0xd0000aaaa0002aa800002bfc015554000015fe00aaaa00000aff005555000000)

def sig1320 : Sig := (0x550000000002a802a802a802a805500550055005405500aa015402a80000008, 0x5500aa00aa02802a80103c3c15401540081e1e0aa00aa0040f0f05500550000)

def sig1330 : Sig := (0x5050000000028282828282828285050505050505145050a0a14142828000004, 0x5050a0a0a0a0282828003333141414140019998a0a0a0a000cccc5050505000)

def sig1336 : Sig := (0xc444400000002222222222222222444444444444451444488891112222000082, 0x844448888888a222222002aaa9111111100155548888888800aaaa4444444480)

def sig1815 : Sig := (0x333326666666199999999999999933333333333330c33326664ccc999955557d, 0x7333266666661999999ffd5554cccccccffeaaaa66666667ff5555333333337f)

def sig2048 : Sig := (0xf0f0e1e1e1e187878787878787870f0f0f0f0f0f0c30f0e1e1c3c387873333fb, 0xf0f0e1e1e1e1f878787ffccccc3c3c3c3ffe66661e1e1e1fff33330f0f0f0fff)

def sig2195 : Sig := (0xf00fe01fe01f807f807f807f807f00ff00ff00ff03f00fe01fc03f807f0f0ff7, 0xf00fe01fe01f87f807fcfc3c3c03fc03fe7e1e1e01fe01ff3f0f0f00ff00ffff)

def sig2347 : Sig := (0xfffe0001fff80007fff80007fff0000ffff0000fff0001fffc0007fff00ffef, 0xfffe0001fff8007ffffd403fc0003ffffea01fe0001fffff500ff0000ffffff)

def sig2512 : Sig := (0xffffe0000000000000007fffffff00000000fffffff00000003fffffff0000de, 0xfffff55555557fffffffcc0003ffffffffe60001fffffffff30000fffffffffe)

def sig2900 : Sig := (0x1fffffff8000000000000000fffffffffffffff000000000000000ffffb1, 0xafffdffffffffffffffbc3fffffffffffde1fffffffffffef0fffffffffffff1)

def sig2903 : Sig := (0x1fffffff8000000000000000ffffffff0000000000000000000000ffff21, 0xaaaaaaa8000000003fffc0000000001fffe0000000000ffff0000000001)

def sig2913 : Sig := (0xfffffffffffffff000000000000000000090, 0x3c0000000000001e0000000000000f000000000000010)

def sig2935 : Sig := (0x1fffe0000000000000000000ffff0000ffff000000000000000000ff0010, 0xa0001fffe0007ff8000003fc03fffc000001fe01fffe000000ff00ffff000000)

def sig2969 : Sig := (0xff01fffffffff807f807f807f80fffffffffffffffff01fe03fc07f80ffffb9, 0xafffdffffffffffffffbc3fffffffffffde1fffffffffffef0fffffffffffff1)

def sig3023 : Sig := (0xf0f1ffffffff878787878787878ffffffffffffffff0f1e1e3c3c7878ffffb5, 0xafffdffffffffffffffbc3fffffffffffde1fffffffffffef0fffffffffffff1)

def sig3063 : Sig := (0xccccdfffffffe666666666666666fffffffffffffffcccd999b3336666ffffb3, 0xafffdffffffffffffffbc3fffffffffffde1fffffffffffef0fffffffffffff1)

def sig3132 : Sig := (0xffffffffffff8000000000000000000000000000000fffffffffffffffffff6f, 0xfffffffffffffffffff83ffffffffffffc1ffffffffffffe0fffffffffffffef)

def sig3133 : Sig := (0x3aaabfffffff8000000000000000000000000000000aaab5556aaad555ffff61, 0x2aaa9555555555555550000002aaaaaaa800000155555554000000aaaaaaaa60)

def sig3163 : Sig := (0xffffe00000000000000000000000000000000000000fffffffffffffff00004e, 0x500020000000000000003c0000000000001e0000000000000f0000000000000e)

def sig3183 : Sig := (0xffffffffffffffff80007fff8000ffff0000ffff000fffffffffffffffffff7f, 0xfffffffffffffffffff83ffffffffffffc1ffffffffffffe0fffffffffffffef)

def sig3205 : Sig := (0xff01fe01fe00000000000000000000000000000000ff01fe03fc07f80f0f008, 0xff01fe01fe07807f80003c3c3fc03fc0001e1e1fe01fe0000f0f0ff00ff0000)

def sig3261 : Sig := (0xf0f1e1e1e1e0000000000000000000000000000000f0f1e1e3c3c7878cccc04, 0xf0f1e1e1e1e07878780033333c3c3c3c0019999e1e1e1e000ccccf0f0f0f000)

def sig3302 : Sig := (0xccccd99999998000000000000000000000000000000cccd999b3336666aaaa02, 0x8cccd9999999e666666002aaab333333300155559999999800aaaacccccccc80)

def sig3452 : Sig := (0xf000e001e0018007800780078007000f000f000f003000e001c00380070303f3, 0xf000e001e0018078007cfc0c0c003c003e7e0606001e001f3f0303000f000fff)

def sig3477 : Sig := (0xfe000001f8000007f8000007f000000ff000003f000001fc000007f000fe7, 0xfe000001f800007fcd4003c000003fe6a001e000001ff35000f000000ffff)

def sig3517 : Sig := (0x1fffffff8000000000000000000000000000000000000000000000ffff21, 0xafffdffffffffffffff803fffffffffffc01fffffffffffe00ffffffffffffe1)

def sig3542 : Sig := (0x300320066006001980198019801900330033003300c0032006400c8019050575, 0x7003200660060198019cfc141400cc00ce7e0a0a006600673f0505003300337f)

def sig3596 : Sig := (0x3030206060600181818181818181030303030303000030206040c08181111179, 0x7030206060601818181ffc44440c0c0c0ffe222206060607ff1111030303037f)

def bank0 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig9, sig10, sig12]

def bank1 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig10, sig14]

def bank2 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig10, sig16]

def bank3 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig9, sig10, sig18]

def bank4 : List Sig := [sig4, sig5, sig6, sig7, sig8, sig9, sig10, sig24]

def bank5 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig10, sig234]

def bank6 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig10, sig234]

def bank7 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig9, sig10, sig234]

def bank8 : List Sig := [sig3, sig5, sig7, sig8, sig9, sig10, sig171]

def bank9 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig10, sig171]

def bank10 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig9, sig10, sig171]

def bank11 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig9, sig10, sig201]

def bank12 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig9, sig10, sig203]

def bank13 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig9, sig10, sig204]

def bank14 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig9, sig10, sig207]

def bank15 : List Sig := [sig3, sig4, sig7, sig8, sig9, sig10, sig26]

def bank16 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig10, sig26]

def bank17 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig10, sig26]

def bank18 : List Sig := [sig3, sig4, sig6, sig8, sig9, sig10, sig101]

def bank19 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig9, sig10, sig101]

def bank20 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig10, sig101]

def bank21 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig10, sig129]

def bank22 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig10, sig130]

def bank23 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig10, sig133]

def bank24 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig10, sig137]

def bank25 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig9, sig10, sig137]

def bank26 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig10, sig137]

def bank27 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig10, sig105]

def bank28 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig10, sig106]

def bank29 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig10, sig109]

def bank30 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig9, sig10, sig30]

def bank31 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig9, sig10, sig32]

def bank32 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig9, sig10, sig33]

def bank33 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig9, sig10, sig42]

def bank34 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig50]

def bank35 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig50]

def bank36 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig10, sig50]

def bank37 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig10]

def bank38 : List Sig := [sig4, sig5, sig6, sig7, sig8, sig9, sig24, sig1299]

def bank39 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig10, sig234, sig1299]

def bank40 : List Sig := [sig3, sig5, sig7, sig8, sig9, sig10, sig171, sig1299]

def bank41 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig9, sig10, sig1336]

def bank42 : List Sig := [sig3, sig4, sig7, sig8, sig9, sig10, sig26, sig1299]

def bank43 : List Sig := [sig3, sig4, sig6, sig8, sig9, sig10, sig101, sig1299]

def bank44 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig10, sig1330]

def bank45 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig10, sig137, sig1299]

def bank46 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig10, sig1320]

def bank47 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig9, sig10, sig1316]

def bank48 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig9, sig10, sig1301]

def bank49 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig50, sig1299]

def bank50 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig1311]

def bank51 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig10, sig1299]

def bank52 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig10, sig1815]

def bank53 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig10, sig2048]

def bank54 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig10, sig2195]

def bank55 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig10, sig2347]

def bank56 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig10, sig2512]

def bank57 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig10, sig234, sig2900]

def bank58 : List Sig := [sig3, sig5, sig7, sig8, sig9, sig10, sig171, sig2900]

def bank59 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig9, sig10, sig3063]

def bank60 : List Sig := [sig3, sig4, sig7, sig8, sig9, sig10, sig26, sig2900]

def bank61 : List Sig := [sig3, sig4, sig6, sig8, sig9, sig10, sig101, sig2900]

def bank62 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig10, sig3023]

def bank63 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig10, sig137, sig2900]

def bank64 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig10, sig2969]

def bank65 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig9, sig10, sig2935]

def bank66 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig9, sig10, sig2903]

def bank67 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig50, sig2900]

def bank68 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig2913]

def bank69 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig10, sig2900]

def bank70 : List Sig := [sig4, sig5, sig6, sig7, sig8, sig9, sig10, sig3133]

def bank71 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig10, sig234, sig3132]

def bank72 : List Sig := [sig3, sig5, sig7, sig8, sig9, sig10, sig171, sig3132]

def bank73 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig9, sig10, sig3302]

def bank74 : List Sig := [sig3, sig4, sig7, sig8, sig9, sig10, sig26, sig3132]

def bank75 : List Sig := [sig3, sig4, sig6, sig8, sig9, sig10, sig101, sig3132]

def bank76 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig10, sig3261]

def bank77 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig10, sig137, sig3132]

def bank78 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig10, sig3205]

def bank79 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig9, sig10, sig3183]

def bank80 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig50, sig3132]

def bank81 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig10, sig3163]

def bank82 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig10, sig3132]

def bank83 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig9, sig10, sig19]

def bank84 : List Sig := [sig4, sig5, sig6, sig7, sig8, sig9, sig24]

def bank85 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig24]

def bank86 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig10, sig234, sig2195]

def bank87 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig10, sig234, sig2347]

def bank88 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig10, sig234, sig2512]

def bank89 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig10, sig234, sig3596]

def bank90 : List Sig := [sig3, sig7, sig8, sig9, sig10, sig16, sig234]

def bank91 : List Sig := [sig3, sig6, sig8, sig9, sig10, sig18, sig234]

def bank92 : List Sig := [sig3, sig6, sig7, sig9, sig10, sig19, sig234]

def bank93 : List Sig := [sig6, sig7, sig8, sig9, sig24, sig234]

def bank94 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig24, sig234]

def bank95 : List Sig := [sig6, sig7, sig8, sig9, sig10, sig24, sig234]

def bank96 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig10, sig135]

def bank97 : List Sig := [sig3, sig8, sig9, sig10, sig137, sig234]

def bank98 : List Sig := [sig3, sig6, sig8, sig9, sig10, sig137, sig234]

def bank99 : List Sig := [sig3, sig7, sig8, sig9, sig10, sig137, sig234]

def bank100 : List Sig := [sig3, sig7, sig8, sig9, sig10, sig105, sig234]

def bank101 : List Sig := [sig3, sig7, sig8, sig9, sig10, sig106, sig234]

def bank102 : List Sig := [sig3, sig7, sig8, sig9, sig109, sig234]

def bank103 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig109, sig234]

def bank104 : List Sig := [sig3, sig7, sig8, sig9, sig10, sig109, sig234]

def bank105 : List Sig := [sig3, sig7, sig8, sig9, sig10, sig273]

def bank106 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig10, sig273]

def bank107 : List Sig := [sig3, sig7, sig8, sig9, sig10, sig234, sig273]

def bank108 : List Sig := [sig3, sig6, sig8, sig9, sig10, sig30, sig234]

def bank109 : List Sig := [sig3, sig6, sig8, sig9, sig10, sig32, sig234]

def bank110 : List Sig := [sig3, sig6, sig8, sig9, sig10, sig33, sig234]

def bank111 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig34, sig234]

def bank112 : List Sig := [sig3, sig6, sig8, sig9, sig10, sig234, sig255]

def bank113 : List Sig := [sig3, sig6, sig7, sig10, sig42, sig234]

def bank114 : List Sig := [sig3, sig6, sig7, sig8, sig10, sig42, sig234]

def bank115 : List Sig := [sig3, sig6, sig7, sig9, sig10, sig42, sig234]

def bank116 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig44, sig234]

def bank117 : List Sig := [sig3, sig6, sig7, sig9, sig10, sig44, sig234]

def bank118 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig10, sig240]

def bank119 : List Sig := [sig3, sig6, sig7, sig8, sig50, sig234]

def bank120 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig50, sig234]

def bank121 : List Sig := [sig3, sig6, sig7, sig8, sig10, sig50, sig234]

def bank122 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig10, sig248]

def bank123 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig234, sig252]

def bank124 : List Sig := [sig3, sig6, sig7, sig8, sig9, sig10, sig253]

def bank125 : List Sig := [sig3, sig5, sig7, sig8, sig9, sig10, sig171, sig2048]

def bank126 : List Sig := [sig3, sig5, sig7, sig8, sig9, sig10, sig171, sig2347]

def bank127 : List Sig := [sig3, sig5, sig7, sig8, sig9, sig10, sig171, sig2512]

def bank128 : List Sig := [sig3, sig5, sig7, sig8, sig9, sig10, sig171, sig3542]

def bank129 : List Sig := [sig3, sig7, sig8, sig9, sig10, sig14, sig171]

def bank130 : List Sig := [sig3, sig5, sig8, sig9, sig10, sig18, sig171]

def bank131 : List Sig := [sig3, sig5, sig7, sig9, sig10, sig19, sig171]

def bank132 : List Sig := [sig5, sig7, sig8, sig9, sig24, sig171]

def bank133 : List Sig := [sig3, sig5, sig7, sig8, sig9, sig24, sig171]

def bank134 : List Sig := [sig5, sig7, sig8, sig9, sig10, sig24, sig171]

def bank135 : List Sig := [sig3, sig5, sig7, sig8, sig9, sig10, sig111]

def bank136 : List Sig := [sig3, sig8, sig9, sig10, sig101, sig171]

def bank137 : List Sig := [sig3, sig5, sig8, sig9, sig10, sig101, sig171]

def bank138 : List Sig := [sig3, sig7, sig8, sig9, sig10, sig101, sig171]

def bank139 : List Sig := [sig3, sig7, sig8, sig9, sig10, sig129, sig171]

def bank140 : List Sig := [sig3, sig7, sig8, sig9, sig10, sig130, sig171]

def bank141 : List Sig := [sig3, sig7, sig8, sig9, sig133, sig171]

def bank142 : List Sig := [sig3, sig5, sig7, sig8, sig9, sig133, sig171]

def bank143 : List Sig := [sig3, sig7, sig8, sig9, sig10, sig133, sig171]

def bank144 : List Sig := [sig3, sig5, sig7, sig8, sig9, sig10, sig273]

def bank145 : List Sig := [sig3, sig7, sig8, sig9, sig10, sig171, sig273]

def bank146 : List Sig := [sig3, sig5, sig8, sig9, sig10, sig30, sig171]

def bank147 : List Sig := [sig3, sig5, sig8, sig9, sig10, sig32, sig171]

def bank148 : List Sig := [sig3, sig5, sig8, sig9, sig10, sig33, sig171]

def bank149 : List Sig := [sig3, sig5, sig7, sig8, sig9, sig34, sig171]

def bank150 : List Sig := [sig3, sig5, sig8, sig9, sig10, sig171, sig188]

def bank151 : List Sig := [sig3, sig5, sig7, sig10, sig42, sig171]

def bank152 : List Sig := [sig3, sig5, sig7, sig8, sig10, sig42, sig171]

def bank153 : List Sig := [sig3, sig5, sig7, sig9, sig10, sig42, sig171]

def bank154 : List Sig := [sig3, sig5, sig7, sig8, sig9, sig44, sig171]

def bank155 : List Sig := [sig3, sig5, sig7, sig9, sig10, sig44, sig171]

def bank156 : List Sig := [sig3, sig5, sig7, sig8, sig9, sig10, sig177]

def bank157 : List Sig := [sig3, sig5, sig7, sig8, sig50, sig171]

def bank158 : List Sig := [sig3, sig5, sig7, sig8, sig9, sig50, sig171]

def bank159 : List Sig := [sig3, sig5, sig7, sig8, sig10, sig50, sig171]

def bank160 : List Sig := [sig3, sig5, sig7, sig8, sig9, sig10, sig180]

def bank161 : List Sig := [sig3, sig5, sig7, sig8, sig9, sig171, sig184]

def bank162 : List Sig := [sig3, sig5, sig7, sig8, sig9, sig10, sig185]

def bank163 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig206]

def bank164 : List Sig := [sig3, sig4, sig7, sig8, sig9, sig10, sig26, sig1815]

def bank165 : List Sig := [sig3, sig4, sig7, sig8, sig9, sig10, sig26, sig2347]

def bank166 : List Sig := [sig3, sig4, sig7, sig8, sig9, sig10, sig26, sig2512]

def bank167 : List Sig := [sig3, sig4, sig7, sig8, sig9, sig10, sig26, sig3452]

def bank168 : List Sig := [sig3, sig7, sig8, sig9, sig10, sig12, sig26]

def bank169 : List Sig := [sig3, sig4, sig8, sig9, sig10, sig18, sig26]

def bank170 : List Sig := [sig3, sig4, sig7, sig9, sig10, sig19, sig26]

def bank171 : List Sig := [sig4, sig7, sig8, sig9, sig24, sig26]

def bank172 : List Sig := [sig3, sig4, sig7, sig8, sig9, sig24, sig26]

def bank173 : List Sig := [sig4, sig7, sig8, sig9, sig10, sig24, sig26]

def bank174 : List Sig := [sig3, sig4, sig7, sig8, sig9, sig10, sig28]

def bank175 : List Sig := [sig3, sig4, sig8, sig9, sig10, sig26, sig201]

def bank176 : List Sig := [sig3, sig7, sig8, sig9, sig10, sig26, sig203]

def bank177 : List Sig := [sig3, sig7, sig8, sig9, sig10, sig26, sig204]

def bank178 : List Sig := [sig3, sig4, sig7, sig8, sig9, sig26, sig206]

def bank179 : List Sig := [sig3, sig7, sig8, sig9, sig10, sig26, sig207]

def bank180 : List Sig := [sig3, sig4, sig7, sig8, sig9, sig10, sig273]

def bank181 : List Sig := [sig3, sig7, sig8, sig9, sig10, sig26, sig273]

def bank182 : List Sig := [sig3, sig4, sig8, sig9, sig10, sig26, sig30]

def bank183 : List Sig := [sig3, sig4, sig8, sig9, sig10, sig26, sig32]

def bank184 : List Sig := [sig3, sig4, sig8, sig9, sig10, sig26, sig33]

def bank185 : List Sig := [sig3, sig4, sig7, sig8, sig9, sig26, sig34]

def bank186 : List Sig := [sig3, sig4, sig8, sig9, sig10, sig38]

def bank187 : List Sig := [sig3, sig4, sig7, sig8, sig9, sig10, sig38]

def bank188 : List Sig := [sig3, sig4, sig8, sig9, sig10, sig26, sig38]

def bank189 : List Sig := [sig3, sig4, sig7, sig8, sig10, sig26, sig42]

def bank190 : List Sig := [sig3, sig4, sig7, sig9, sig10, sig26, sig42]

def bank191 : List Sig := [sig3, sig4, sig7, sig8, sig9, sig26, sig44]

def bank192 : List Sig := [sig3, sig4, sig7, sig9, sig10, sig26, sig44]

def bank193 : List Sig := [sig3, sig4, sig7, sig8, sig9, sig10, sig62]

def bank194 : List Sig := [sig3, sig4, sig7, sig8, sig26, sig50]

def bank195 : List Sig := [sig3, sig4, sig7, sig8, sig9, sig26, sig50]

def bank196 : List Sig := [sig3, sig4, sig7, sig8, sig10, sig26, sig50]

def bank197 : List Sig := [sig3, sig4, sig7, sig8, sig9, sig10, sig80]

def bank198 : List Sig := [sig3, sig4, sig7, sig8, sig9, sig83]

def bank199 : List Sig := [sig3, sig4, sig7, sig8, sig9, sig10, sig83]

def bank200 : List Sig := [sig3, sig4, sig7, sig8, sig9, sig26, sig83]

def bank201 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig9, sig133]

def bank202 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig133]

def bank203 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig10, sig137, sig1815]

def bank204 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig10, sig137, sig2048]

def bank205 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig10, sig137, sig2512]

def bank206 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig10, sig137, sig3477]

def bank207 : List Sig := [sig3, sig5, sig8, sig9, sig10, sig12, sig137]

def bank208 : List Sig := [sig3, sig4, sig8, sig9, sig10, sig14, sig137]

def bank209 : List Sig := [sig3, sig4, sig5, sig9, sig10, sig19, sig137]

def bank210 : List Sig := [sig4, sig5, sig8, sig9, sig24, sig137]

def bank211 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig24, sig137]

def bank212 : List Sig := [sig4, sig5, sig8, sig9, sig10, sig24, sig137]

def bank213 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig10, sig139]

def bank214 : List Sig := [sig3, sig4, sig8, sig9, sig10, sig137, sig234]

def bank215 : List Sig := [sig3, sig5, sig8, sig9, sig10, sig137, sig234]

def bank216 : List Sig := [sig3, sig5, sig8, sig9, sig10, sig137, sig203]

def bank217 : List Sig := [sig3, sig5, sig8, sig9, sig10, sig137, sig204]

def bank218 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig137, sig206]

def bank219 : List Sig := [sig3, sig5, sig8, sig9, sig10, sig137, sig207]

def bank220 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig10, sig188]

def bank221 : List Sig := [sig3, sig4, sig8, sig9, sig10, sig129, sig137]

def bank222 : List Sig := [sig3, sig4, sig8, sig9, sig10, sig130, sig137]

def bank223 : List Sig := [sig3, sig4, sig8, sig9, sig133, sig137]

def bank224 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig133, sig137]

def bank225 : List Sig := [sig3, sig4, sig8, sig9, sig10, sig133, sig137]

def bank226 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig10, sig38]

def bank227 : List Sig := [sig3, sig4, sig8, sig9, sig10, sig38, sig137]

def bank228 : List Sig := [sig3, sig4, sig5, sig8, sig10, sig42, sig137]

def bank229 : List Sig := [sig3, sig4, sig5, sig9, sig10, sig42, sig137]

def bank230 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig44, sig137]

def bank231 : List Sig := [sig3, sig4, sig5, sig9, sig10, sig44, sig137]

def bank232 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig10, sig143]

def bank233 : List Sig := [sig3, sig4, sig5, sig8, sig50, sig137]

def bank234 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig50, sig137]

def bank235 : List Sig := [sig3, sig4, sig5, sig8, sig10, sig50, sig137]

def bank236 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig137, sig156]

def bank237 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig9, sig109]

def bank238 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig109]

def bank239 : List Sig := [sig4, sig5, sig6, sig8, sig9, sig10, sig465]

def bank240 : List Sig := [sig3, sig5, sig6, sig8, sig9, sig10, sig995]

def bank241 : List Sig := [sig3, sig4, sig6, sig8, sig9, sig33, sig133]

def bank242 : List Sig := [sig3, sig4, sig6, sig8, sig9, sig10, sig758]

def bank243 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig33, sig109]

def bank244 : List Sig := [sig3, sig4, sig5, sig8, sig9, sig10, sig551]

def bank245 : List Sig := [sig3, sig4, sig5, sig6, sig9, sig33, sig44]

def bank246 : List Sig := [sig3, sig4, sig5, sig6, sig9, sig10, sig474]

def bank247 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig33, sig50]

def bank248 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig10, sig461]

def bank249 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig34]

def bank250 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig10, sig42]

def bank251 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig10, sig42]

def bank252 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig9, sig44]

def bank253 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig9, sig44]

def bank254 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig9, sig10, sig44]

def bank255 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig50, sig1815]

def bank256 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig50, sig2048]

def bank257 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig50, sig2195]

def bank258 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig50, sig2347]

def bank259 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig50, sig2512]

def bank260 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig50, sig3517]

def bank261 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig12, sig50]

def bank262 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig14, sig50]

def bank263 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig16, sig50]

def bank264 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig18, sig50]

def bank265 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig19, sig50]

def bank266 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig50, sig234]

def bank267 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig50, sig234]

def bank268 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig50, sig171]

def bank269 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig50, sig171]

def bank270 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig50, sig201]

def bank271 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig50, sig203]

def bank272 : List Sig := [sig3, sig5, sig6, sig7, sig8, sig50, sig210]

def bank273 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig26, sig50]

def bank274 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig26, sig50]

def bank275 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig50, sig101]

def bank276 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig50, sig101]

def bank277 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig50, sig129]

def bank278 : List Sig := [sig3, sig4, sig6, sig7, sig8, sig50, sig162]

def bank279 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig50, sig137]

def bank280 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig50, sig137]

def bank281 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig50, sig105]

def bank282 : List Sig := [sig3, sig4, sig5, sig7, sig8, sig50, sig159]

def bank283 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig30, sig50]

def bank284 : List Sig := [sig3, sig4, sig5, sig6, sig8, sig50, sig65]

def bank285 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig8, sig68]

def bank286 : List Sig := [sig3, sig4, sig5, sig6, sig7, sig50, sig68]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded0 : Blocked 7 0 bank0 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded1 : Blocked 7 0 bank1 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded2 : Blocked 7 0 bank2 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded3 : Blocked 7 0 bank3 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded4 : Blocked 7 0 bank4 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded5 : Blocked 7 0 bank5 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded6 : Blocked 7 0 bank6 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded7 : Blocked 7 0 bank7 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded8 : Blocked 7 0 bank8 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded9 : Blocked 7 0 bank9 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded10 : Blocked 7 0 bank10 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded11 : Blocked 7 0 bank11 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded12 : Blocked 7 0 bank12 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded13 : Blocked 7 0 bank13 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded14 : Blocked 7 0 bank14 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded15 : Blocked 7 0 bank15 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded16 : Blocked 7 0 bank16 :=
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

theorem excluded37 : Blocked 8 0 bank37 :=
  block_step [] [bank0, bank1, bank2, bank3, bank4, bank5, bank6, bank7, bank8, bank9, bank10, bank11, bank12, bank13, bank14, bank15, bank16, bank17, bank18, bank19, bank20, bank21, bank22, bank23, bank24, bank25, bank26, bank27, bank28, bank29, bank30, bank31, bank32, bank33, bank34, bank35, bank36]
    True.intro
    ⟨excluded0, excluded1, excluded2, excluded3, excluded4, excluded5, excluded6, excluded7, excluded8, excluded9, excluded10, excluded11, excluded12, excluded13, excluded14, excluded15, excluded16, excluded17, excluded18, excluded19, excluded20, excluded21, excluded22, excluded23, excluded24, excluded25, excluded26, excluded27, excluded28, excluded29, excluded30, excluded31, excluded32, excluded33, excluded34, excluded35, excluded36, True.intro⟩
    (by decide +kernel) (by decide +kernel)

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

theorem excluded42 : Blocked 7 0 bank42 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded43 : Blocked 7 0 bank43 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded44 : Blocked 7 0 bank44 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded45 : Blocked 7 0 bank45 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded46 : Blocked 7 0 bank46 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded47 : Blocked 7 0 bank47 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded48 : Blocked 7 0 bank48 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded49 : Blocked 7 0 bank49 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded50 : Blocked 7 0 bank50 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded51 : Blocked 8 0 bank51 :=
  block_step [] [bank38, bank39, bank40, bank41, bank42, bank43, bank44, bank45, bank46, bank47, bank48, bank49, bank50]
    True.intro
    ⟨excluded38, excluded39, excluded40, excluded41, excluded42, excluded43, excluded44, excluded45, excluded46, excluded47, excluded48, excluded49, excluded50, True.intro⟩
    (by decide +kernel) (by decide +kernel)

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

theorem excluded57 : Blocked 7 0 bank57 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded58 : Blocked 7 0 bank58 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded59 : Blocked 7 0 bank59 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded60 : Blocked 7 0 bank60 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded61 : Blocked 7 0 bank61 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded62 : Blocked 7 0 bank62 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded63 : Blocked 7 0 bank63 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded64 : Blocked 7 0 bank64 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded65 : Blocked 7 0 bank65 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded66 : Blocked 7 0 bank66 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded67 : Blocked 7 0 bank67 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded68 : Blocked 7 0 bank68 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded69 : Blocked 8 0 bank69 :=
  block_step [] [bank57, bank58, bank59, bank60, bank61, bank62, bank63, bank64, bank65, bank66, bank67, bank68]
    True.intro
    ⟨excluded57, excluded58, excluded59, excluded60, excluded61, excluded62, excluded63, excluded64, excluded65, excluded66, excluded67, excluded68, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded70 : Blocked 7 0 bank70 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded71 : Blocked 7 0 bank71 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded72 : Blocked 7 0 bank72 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded73 : Blocked 7 0 bank73 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded74 : Blocked 7 0 bank74 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded75 : Blocked 7 0 bank75 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded76 : Blocked 7 0 bank76 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded77 : Blocked 7 0 bank77 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded78 : Blocked 7 0 bank78 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded79 : Blocked 7 0 bank79 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded80 : Blocked 7 0 bank80 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded81 : Blocked 7 0 bank81 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded82 : Blocked 8 0 bank82 :=
  block_step [] [bank70, bank71, bank72, bank73, bank74, bank75, bank76, bank77, bank78, bank79, bank80, bank81]
    True.intro
    ⟨excluded70, excluded71, excluded72, excluded73, excluded74, excluded75, excluded76, excluded77, excluded78, excluded79, excluded80, excluded81, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded83 : Blocked 8 1 bank0 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded84 : Blocked 8 1 bank1 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded85 : Blocked 8 1 bank2 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded86 : Blocked 8 1 bank3 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded87 : Blocked 8 1 bank83 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded88 : Blocked 8 1 bank84 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded89 : Blocked 8 1 bank85 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded90 : Blocked 8 1 bank4 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded91 : Blocked 7 0 bank86 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded92 : Blocked 7 0 bank87 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded93 : Blocked 7 0 bank88 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded94 : Blocked 7 0 bank89 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded95 : Blocked 7 1 bank90 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded96 : Blocked 7 1 bank91 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded97 : Blocked 7 1 bank92 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded98 : Blocked 7 1 bank93 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded99 : Blocked 7 1 bank94 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded100 : Blocked 7 1 bank95 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded101 : Blocked 7 1 bank96 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded102 : Blocked 7 1 bank97 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded103 : Blocked 7 1 bank98 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded104 : Blocked 7 1 bank99 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded105 : Blocked 7 1 bank100 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded106 : Blocked 7 1 bank101 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded107 : Blocked 7 1 bank102 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded108 : Blocked 7 1 bank103 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded109 : Blocked 7 1 bank104 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded110 : Blocked 7 1 bank105 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded111 : Blocked 7 1 bank106 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded112 : Blocked 7 1 bank107 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded113 : Blocked 7 1 bank108 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded114 : Blocked 7 1 bank109 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded115 : Blocked 7 1 bank110 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded116 : Blocked 7 1 bank111 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded117 : Blocked 7 1 bank112 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded118 : Blocked 7 1 bank113 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded119 : Blocked 7 1 bank114 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded120 : Blocked 7 1 bank115 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded121 : Blocked 7 1 bank116 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded122 : Blocked 7 1 bank117 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded123 : Blocked 7 1 bank118 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded124 : Blocked 7 1 bank119 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded125 : Blocked 7 1 bank120 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded126 : Blocked 7 1 bank121 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded127 : Blocked 7 1 bank122 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded128 : Blocked 7 1 bank123 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded129 : Blocked 7 1 bank124 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded130 : Blocked 8 1 bank5 :=
  block_step [bank39, bank86, bank87, bank88, bank57, bank71, bank89] [bank90, bank91, bank92, bank93, bank94, bank95, bank96, bank97, bank98, bank99, bank100, bank101, bank102, bank103, bank104, bank105, bank106, bank107, bank108, bank109, bank110, bank111, bank112, bank113, bank114, bank115, bank116, bank117, bank118, bank119, bank120, bank121, bank122, bank123, bank124]
    ⟨excluded39, excluded91, excluded92, excluded93, excluded57, excluded71, excluded94, True.intro⟩
    ⟨excluded95, excluded96, excluded97, excluded98, excluded99, excluded100, excluded101, excluded102, excluded103, excluded104, excluded105, excluded106, excluded107, excluded108, excluded109, excluded110, excluded111, excluded112, excluded113, excluded114, excluded115, excluded116, excluded117, excluded118, excluded119, excluded120, excluded121, excluded122, excluded123, excluded124, excluded125, excluded126, excluded127, excluded128, excluded129, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded131 : Blocked 8 1 bank6 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded132 : Blocked 8 1 bank7 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded133 : Blocked 7 0 bank125 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded134 : Blocked 7 0 bank126 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded135 : Blocked 7 0 bank127 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded136 : Blocked 7 0 bank128 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded137 : Blocked 7 1 bank129 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded138 : Blocked 7 1 bank130 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded139 : Blocked 7 1 bank131 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded140 : Blocked 7 1 bank132 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded141 : Blocked 7 1 bank133 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded142 : Blocked 7 1 bank134 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded143 : Blocked 7 1 bank135 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded144 : Blocked 7 1 bank136 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded145 : Blocked 7 1 bank137 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded146 : Blocked 7 1 bank138 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded147 : Blocked 7 1 bank139 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded148 : Blocked 7 1 bank140 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded149 : Blocked 7 1 bank141 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded150 : Blocked 7 1 bank142 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded151 : Blocked 7 1 bank143 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded152 : Blocked 7 1 bank144 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded153 : Blocked 7 1 bank145 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded154 : Blocked 7 1 bank146 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded155 : Blocked 7 1 bank147 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded156 : Blocked 7 1 bank148 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded157 : Blocked 7 1 bank149 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded158 : Blocked 7 1 bank150 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded159 : Blocked 7 1 bank151 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded160 : Blocked 7 1 bank152 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded161 : Blocked 7 1 bank153 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded162 : Blocked 7 1 bank154 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded163 : Blocked 7 1 bank155 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded164 : Blocked 7 1 bank156 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded165 : Blocked 7 1 bank157 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded166 : Blocked 7 1 bank158 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded167 : Blocked 7 1 bank159 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded168 : Blocked 7 1 bank160 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded169 : Blocked 7 1 bank161 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded170 : Blocked 7 1 bank162 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded171 : Blocked 8 1 bank8 :=
  block_step [bank40, bank125, bank126, bank127, bank58, bank72, bank128] [bank129, bank130, bank131, bank132, bank133, bank134, bank135, bank136, bank137, bank138, bank139, bank140, bank141, bank142, bank143, bank105, bank144, bank145, bank146, bank147, bank148, bank149, bank150, bank151, bank152, bank153, bank154, bank155, bank156, bank157, bank158, bank159, bank160, bank161, bank162]
    ⟨excluded40, excluded133, excluded134, excluded135, excluded58, excluded72, excluded136, True.intro⟩
    ⟨excluded137, excluded138, excluded139, excluded140, excluded141, excluded142, excluded143, excluded144, excluded145, excluded146, excluded147, excluded148, excluded149, excluded150, excluded151, excluded110, excluded152, excluded153, excluded154, excluded155, excluded156, excluded157, excluded158, excluded159, excluded160, excluded161, excluded162, excluded163, excluded164, excluded165, excluded166, excluded167, excluded168, excluded169, excluded170, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded172 : Blocked 8 1 bank9 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded173 : Blocked 8 1 bank10 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded174 : Blocked 8 1 bank11 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded175 : Blocked 8 1 bank12 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded176 : Blocked 8 1 bank13 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded177 : Blocked 8 1 bank163 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded178 : Blocked 8 1 bank14 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded179 : Blocked 7 0 bank164 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded180 : Blocked 7 0 bank165 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded181 : Blocked 7 0 bank166 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded182 : Blocked 7 0 bank167 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded183 : Blocked 7 1 bank168 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded184 : Blocked 7 1 bank169 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded185 : Blocked 7 1 bank170 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded186 : Blocked 7 1 bank171 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded187 : Blocked 7 1 bank172 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded188 : Blocked 7 1 bank173 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded189 : Blocked 7 1 bank174 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded190 : Blocked 7 1 bank175 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded191 : Blocked 7 1 bank176 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded192 : Blocked 7 1 bank177 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded193 : Blocked 7 1 bank178 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded194 : Blocked 7 1 bank179 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded195 : Blocked 7 1 bank180 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded196 : Blocked 7 1 bank181 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded197 : Blocked 7 1 bank182 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded198 : Blocked 7 1 bank183 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded199 : Blocked 7 1 bank184 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded200 : Blocked 7 1 bank185 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded201 : Blocked 7 1 bank186 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded202 : Blocked 7 1 bank187 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded203 : Blocked 7 1 bank188 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded204 : Blocked 7 1 bank189 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded205 : Blocked 7 1 bank190 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded206 : Blocked 7 1 bank191 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded207 : Blocked 7 1 bank192 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded208 : Blocked 7 1 bank193 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded209 : Blocked 7 1 bank194 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded210 : Blocked 7 1 bank195 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded211 : Blocked 7 1 bank196 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded212 : Blocked 7 1 bank197 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded213 : Blocked 7 1 bank198 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded214 : Blocked 7 1 bank199 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded215 : Blocked 7 1 bank200 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded216 : Blocked 8 1 bank15 :=
  block_step [bank42, bank164, bank165, bank166, bank60, bank74, bank167] [bank168, bank169, bank170, bank171, bank172, bank173, bank174, bank175, bank176, bank177, bank178, bank179, bank105, bank180, bank181, bank182, bank183, bank184, bank185, bank186, bank187, bank188, bank189, bank190, bank191, bank192, bank193, bank194, bank195, bank196, bank197, bank198, bank199, bank200]
    ⟨excluded42, excluded179, excluded180, excluded181, excluded60, excluded74, excluded182, True.intro⟩
    ⟨excluded183, excluded184, excluded185, excluded186, excluded187, excluded188, excluded189, excluded190, excluded191, excluded192, excluded193, excluded194, excluded110, excluded195, excluded196, excluded197, excluded198, excluded199, excluded200, excluded201, excluded202, excluded203, excluded204, excluded205, excluded206, excluded207, excluded208, excluded209, excluded210, excluded211, excluded212, excluded213, excluded214, excluded215, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded217 : Blocked 8 1 bank16 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded218 : Blocked 8 1 bank17 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded219 : Blocked 8 1 bank18 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded220 : Blocked 8 1 bank19 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded221 : Blocked 8 1 bank20 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded222 : Blocked 8 1 bank21 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded223 : Blocked 8 1 bank22 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded224 : Blocked 8 1 bank201 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded225 : Blocked 8 1 bank202 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded226 : Blocked 8 1 bank23 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded227 : Blocked 7 0 bank203 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded228 : Blocked 7 0 bank204 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded229 : Blocked 7 0 bank205 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded230 : Blocked 7 0 bank206 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded231 : Blocked 7 1 bank207 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded232 : Blocked 7 1 bank208 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded233 : Blocked 7 1 bank209 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded234 : Blocked 7 1 bank210 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded235 : Blocked 7 1 bank211 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded236 : Blocked 7 1 bank212 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded237 : Blocked 7 1 bank213 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded238 : Blocked 7 1 bank214 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded239 : Blocked 7 1 bank215 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded240 : Blocked 7 1 bank216 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded241 : Blocked 7 1 bank217 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded242 : Blocked 7 1 bank218 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded243 : Blocked 7 1 bank219 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded244 : Blocked 7 1 bank220 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded245 : Blocked 7 1 bank221 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded246 : Blocked 7 1 bank222 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded247 : Blocked 7 1 bank223 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded248 : Blocked 7 1 bank224 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded249 : Blocked 7 1 bank225 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded250 : Blocked 7 1 bank226 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded251 : Blocked 7 1 bank227 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded252 : Blocked 7 1 bank228 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded253 : Blocked 7 1 bank229 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded254 : Blocked 7 1 bank230 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded255 : Blocked 7 1 bank231 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded256 : Blocked 7 1 bank232 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded257 : Blocked 7 1 bank233 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded258 : Blocked 7 1 bank234 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded259 : Blocked 7 1 bank235 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded260 : Blocked 7 1 bank236 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded261 : Blocked 8 1 bank24 :=
  block_step [bank45, bank203, bank204, bank205, bank63, bank77, bank206] [bank207, bank208, bank209, bank210, bank211, bank212, bank213, bank97, bank214, bank215, bank216, bank217, bank218, bank219, bank220, bank221, bank222, bank223, bank224, bank225, bank186, bank226, bank227, bank228, bank229, bank230, bank231, bank232, bank233, bank234, bank235, bank236]
    ⟨excluded45, excluded227, excluded228, excluded229, excluded63, excluded77, excluded230, True.intro⟩
    ⟨excluded231, excluded232, excluded233, excluded234, excluded235, excluded236, excluded237, excluded102, excluded238, excluded239, excluded240, excluded241, excluded242, excluded243, excluded244, excluded245, excluded246, excluded247, excluded248, excluded249, excluded201, excluded250, excluded251, excluded252, excluded253, excluded254, excluded255, excluded256, excluded257, excluded258, excluded259, excluded260, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded262 : Blocked 8 1 bank25 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded263 : Blocked 8 1 bank26 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded264 : Blocked 8 1 bank27 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded265 : Blocked 8 1 bank28 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded266 : Blocked 8 1 bank237 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded267 : Blocked 8 1 bank238 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded268 : Blocked 8 1 bank29 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded269 : Blocked 8 1 bank30 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded270 : Blocked 8 1 bank31 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded271 : Blocked 7 1 bank239 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded272 : Blocked 7 1 bank240 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded273 : Blocked 7 1 bank241 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded274 : Blocked 7 1 bank242 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded275 : Blocked 7 1 bank243 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded276 : Blocked 7 1 bank244 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded277 : Blocked 7 1 bank245 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded278 : Blocked 7 1 bank246 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded279 : Blocked 7 1 bank247 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded280 : Blocked 7 1 bank248 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded281 : Blocked 8 1 bank32 :=
  block_step [] [bank239, bank110, bank148, bank240, bank184, bank241, bank242, bank243, bank244, bank245, bank246, bank247, bank248]
    True.intro
    ⟨excluded271, excluded115, excluded156, excluded272, excluded199, excluded273, excluded274, excluded275, excluded276, excluded277, excluded278, excluded279, excluded280, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded282 : Blocked 8 1 bank249 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded283 : Blocked 8 1 bank250 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded284 : Blocked 8 1 bank251 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded285 : Blocked 8 1 bank33 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded286 : Blocked 8 1 bank252 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded287 : Blocked 8 1 bank253 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded288 : Blocked 8 1 bank254 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded289 : Blocked 7 0 bank255 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded290 : Blocked 7 0 bank256 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded291 : Blocked 7 0 bank257 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded292 : Blocked 7 0 bank258 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded293 : Blocked 7 0 bank259 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded294 : Blocked 7 0 bank260 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded295 : Blocked 7 1 bank261 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded296 : Blocked 7 1 bank262 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded297 : Blocked 7 1 bank263 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded298 : Blocked 7 1 bank264 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded299 : Blocked 7 1 bank265 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded300 : Blocked 7 1 bank266 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded301 : Blocked 7 1 bank267 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded302 : Blocked 7 1 bank268 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded303 : Blocked 7 1 bank269 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded304 : Blocked 7 1 bank270 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded305 : Blocked 7 1 bank271 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded306 : Blocked 7 1 bank272 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded307 : Blocked 7 1 bank273 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded308 : Blocked 7 1 bank274 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded309 : Blocked 7 1 bank275 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded310 : Blocked 7 1 bank276 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded311 : Blocked 7 1 bank277 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded312 : Blocked 7 1 bank278 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded313 : Blocked 7 1 bank279 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded314 : Blocked 7 1 bank280 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded315 : Blocked 7 1 bank281 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded316 : Blocked 7 1 bank282 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded317 : Blocked 7 1 bank283 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded318 : Blocked 7 1 bank284 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded319 : Blocked 7 1 bank285 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded320 : Blocked 7 1 bank286 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded321 : Blocked 8 1 bank34 :=
  block_step [bank49, bank255, bank256, bank257, bank258, bank259, bank260] [bank261, bank262, bank263, bank264, bank265, bank119, bank266, bank267, bank157, bank268, bank269, bank270, bank271, bank272, bank194, bank273, bank274, bank275, bank276, bank277, bank278, bank233, bank279, bank280, bank281, bank282, bank283, bank284, bank285, bank286]
    ⟨excluded49, excluded289, excluded290, excluded291, excluded292, excluded293, excluded294, True.intro⟩
    ⟨excluded295, excluded296, excluded297, excluded298, excluded299, excluded124, excluded300, excluded301, excluded165, excluded302, excluded303, excluded304, excluded305, excluded306, excluded209, excluded307, excluded308, excluded309, excluded310, excluded311, excluded312, excluded257, excluded313, excluded314, excluded315, excluded316, excluded317, excluded318, excluded319, excluded320, True.intro⟩
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded322 : Blocked 8 1 bank35 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded323 : Blocked 8 1 bank36 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

theorem excluded324 : Blocked 9 1 bank37 :=
  block_step [bank51, bank52, bank53, bank54, bank55, bank56, bank69, bank82] [bank0, bank1, bank2, bank3, bank83, bank84, bank85, bank4, bank5, bank6, bank7, bank8, bank9, bank10, bank11, bank12, bank13, bank163, bank14, bank15, bank16, bank17, bank18, bank19, bank20, bank21, bank22, bank201, bank202, bank23, bank24, bank25, bank26, bank27, bank28, bank237, bank238, bank29, bank30, bank31, bank32, bank249, bank250, bank251, bank33, bank252, bank253, bank254, bank34, bank35, bank36]
    ⟨excluded51, excluded52, excluded53, excluded54, excluded55, excluded56, excluded69, excluded82, True.intro⟩
    ⟨excluded83, excluded84, excluded85, excluded86, excluded87, excluded88, excluded89, excluded90, excluded130, excluded131, excluded132, excluded171, excluded172, excluded173, excluded174, excluded175, excluded176, excluded177, excluded178, excluded216, excluded217, excluded218, excluded219, excluded220, excluded221, excluded222, excluded223, excluded224, excluded225, excluded226, excluded261, excluded262, excluded263, excluded264, excluded265, excluded266, excluded267, excluded268, excluded269, excluded270, excluded281, excluded282, excluded283, excluded284, excluded285, excluded286, excluded287, excluded288, excluded321, excluded322, excluded323, True.intro⟩
    (by decide +kernel) (by decide +kernel)

theorem zero_excluded : Blocked 8 0 root := excluded37

theorem one_excluded : Blocked 9 1 root := excluded324

end PEqualNP.Outside.L_meta_14874_aux

open PEqualNP.Outside.L_meta_14874_aux


theorem PEqualNP.Outside.L_meta_14874 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
