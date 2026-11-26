import PEqualNP.Defs
import PEqualNP.Library.Helpers.PromiseColTree

namespace PEqualNP.Outside.L_meta_19143
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Library.Helpers.PromiseColTree

def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1,t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [
(true,21,58),(true,6,36),(true,25,64),(true,18,52),(true,10,35),(true,1,33),(true,0,54),(true,4,62),(true,15,42),(true,47,70),(true,9,39),(true,24,54),
(true,28,52),(true,27,75),(true,10,65),(true,13,44),(true,61,74),(true,5,20),(true,17,45),(true,26,51),(true,25,59),(true,3,41),(true,12,55),(true,28,38),
(true,8,16),(true,30,40),(true,13,57),(true,0,62),(true,9,67),(true,4,43),(true,29,48),(true,39,48),(true,3,47),(true,61,73),(true,36,60),(true,11,89),
(true,19,52),(true,53,78),(true,28,50),(true,2,68),(true,76,81),(true,18,55),(true,34,91),(true,1,8),(true,107,24),(true,11,83),(true,109,85),(true,66,69),
(true,111,104),(true,77,98),(true,113,104),(true,32,43),(true,115,45),(true,116,95),(true,16,73),(true,118,87),(true,119,94),(true,53,74),(true,121,81),(true,122,106),
(true,25,35),(true,124,72),(true,125,100),(true,24,46),(true,127,82),(true,128,99),(true,69,72),(true,130,79),(true,131,102),(true,19,31),(true,133,82),(true,134,97),
(true,31,80),(true,136,84),(true,137,86),(true,14,43),(true,139,78),(true,140,97),(true,20,29),(true,142,33),(true,143,68),(true,144,90),(true,4,15),(true,146,41),
(true,147,80),(true,148,102),(true,24,37),(true,150,51),(true,151,59),(true,152,92),(true,40,42),(true,154,71),(true,155,85),(true,156,88),(true,2,35),(true,158,54),
(true,159,92),(true,160,94),(true,6,14),(true,162,50),(true,163,60),(true,164,66),(true,23,34),(true,166,40),(true,167,72),(true,168,105),(true,37,65),(true,170,74),
(true,171,96),(true,172,103),(true,26,46),(true,174,64),(true,175,77),(true,176,93),(true,7,22),(true,178,43),(true,179,84),(true,180,106),(true,0,21),(true,182,32),
(true,183,41),(true,184,101),(true,14,46),(true,186,71),(true,187,79),(true,188,100),(true,28,32),(true,190,37),(true,191,60),(true,192,99),(true,26,69),(true,194,71),
(true,195,95),(true,196,96),(true,23,25),(true,198,56),(true,199,98),(true,200,103),(true,15,49),(true,202,63),(true,203,66),(true,204,93),(true,22,36),(true,206,45),
(true,207,63),(true,208,83),(true,209,88),(true,2,27),(true,211,42),(true,212,61),(true,213,90),(true,214,105),(true,8,44),(true,216,67),(true,217,86),(true,218,87),
(true,219,101),(false,205,161),(false,201,197),(false,141,193),(false,138,114),(false,189,185),(false,132,181),(false,177,173),(false,169,165),(false,215,120),(false,210,123),(false,157,153),
(false,126,129),(false,149,145),(false,135,220),(false,112,110),(false,108,117),(true,221,222),(true,223,224),(true,225,226),(true,227,228),(true,229,230),(true,231,232),(true,233,234),
(true,235,236),(true,237,238),(true,239,240),(true,241,242),(true,243,244),(true,245,246),(true,247,248),(true,249,250)]

def circuit : Circuit := ⟨codes.map asGate, 251⟩
def rows : List ℕ := ([0xf2bc7573, 0x59092a9d, 0xc443c8c2, 0x1d58483a, 0x1b7982bb, 0xa8882290, 0x74d0fd25, 0x00041402, 0x6879a8a5, 0xd65a6f1a, 0x7455fba3, 0x24508c1a, 0x3050a010, 0x68658ad5, 0x10a00735, 0x5e55690e, 0x6ab804a4, 0x00b01458, 0xf447af40, 0x00b07351, 0xa88c2290, 0x40d9d7bc, 0x40241486, 0x54058082, 0x6891afb9, 0x50ddf79e, 0x553080be, 0x28c180f8, 0x6ac8ae9e, 0xa6860e80, 0x20508c18, 0x10f01050] : List ℕ)

theorem fan : FanInTwo circuit := by
  intro g hg
  obtain ⟨⟨b,i,j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

theorem good : PEqualNP.Represents.Represents
    (fun u v : Fin 32 => (rows.getD u.val 0).testBit v.val) circuit := by
  apply represents_of_tcols (N := 10) (D := 8) (by decide) circuit rows
  · have hh : rows.all (fun x => decide (x < 2 ^ 32)) = true := by decide +kernel
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hh x hx)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end PEqualNP.Outside.L_meta_19143

open PEqualNP.Outside.L_meta_19143
theorem PEqualNP.Outside.L_meta_19143 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 190 ∧ PEqualNP.Represents.Represents (fun u v : Fin 32 => (([0xf2bc7573, 0x59092a9d, 0xc443c8c2, 0x1d58483a, 0x1b7982bb, 0xa8882290, 0x74d0fd25, 0x00041402, 0x6879a8a5, 0xd65a6f1a, 0x7455fba3, 0x24508c1a, 0x3050a010, 0x68658ad5, 0x10a00735, 0x5e55690e, 0x6ab804a4, 0x00b01458, 0xf447af40, 0x00b07351, 0xa88c2290, 0x40d9d7bc, 0x40241486, 0x54058082, 0x6891afb9, 0x50ddf79e, 0x553080be, 0x28c180f8, 0x6ac8ae9e, 0xa6860e80, 0x20508c18, 0x10f01050] : List ℕ).getD u.val 0).testBit v.val) C := by
  exact ⟨circuit, fan, by decide +kernel, good⟩
