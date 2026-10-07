import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

namespace QepInterior
noncomputable section
abbrev Code := Fin 4
abbrev Samples := ℝ × ℝ
abbrev Message := Code × Code × Code

def value (q : Code) : ℝ := q.val

def input : Samples := (-1, 1)
def step (w : ℝ) (x : Samples) : Samples := (max 0 (w*x.1), max 0 (w*x.2))
def sqError (x y : Samples) : ℝ := (x.1-y.1)^2 + (x.2-y.2)^2
def frobError (x y : Samples) : ℝ := Real.sqrt (sqError x y)
def gram (x : Samples) : ℝ := x.1^2 + x.2^2


def qepLoss (w : ℝ) (x y : Samples) (q : Code) : ℝ :=
  (w*x.1-value q*y.1)^2 + (w*x.2-value q*y.2)^2

def baseLoss (w : ℝ) (y : Samples) (q : Code) : ℝ := qepLoss w y y q

def corrected (w : ℝ) (x y : Samples) : ℝ :=
  w + w*((x.1-y.1)*y.1+(x.2-y.2)*y.2)/gram y


def pick (f : Code → ℝ) : Code :=
  if f 0 ≤ f 1 ∧ f 0 ≤ f 2 ∧ f 0 ≤ f 3 then 0
  else if f 1 ≤ f 2 ∧ f 1 ≤ f 3 then 1
  else if f 2 ≤ f 3 then 2 else 3

def nearest (t : ℝ) : Code := pick (fun q => (t-value q)^2)
def StrictMin (f : Code → ℝ) (k : Code) : Prop := ∀ q, q ≠ k → f k < f q

theorem pick_min (f : Code → ℝ) (q : Code) : f (pick f) ≤ f q := by
  by_cases h01 : f 0 ≤ f 1 <;> by_cases h02 : f 0 ≤ f 2 <;>
    by_cases h03 : f 0 ≤ f 3 <;> by_cases h12 : f 1 ≤ f 2 <;>
    by_cases h13 : f 1 ≤ f 3 <;> by_cases h23 : f 2 ≤ f 3 <;>
    simp only [pick, h01, h02, h03, h12, h13, h23, and_true, and_false, ite_true, ite_false] <;>
    fin_cases q <;> norm_num at * <;> linarith

theorem pick_tie (f : Code → ℝ) (q : Code) (h : f q = f (pick f)) : pick f ≤ q := by
  by_cases h01 : f 0 ≤ f 1 <;> by_cases h02 : f 0 ≤ f 2 <;>
    by_cases h03 : f 0 ≤ f 3 <;> by_cases h12 : f 1 ≤ f 2 <;>
    by_cases h13 : f 1 ≤ f 3 <;> by_cases h23 : f 2 ≤ f 3 <;>
    simp only [pick, h01, h02, h03, h12, h13, h23, and_true, and_false, ite_true, ite_false] at h ⊢ <;>
    fin_cases q <;> norm_num at * <;> linarith

theorem pick_of_strict {f : Code → ℝ} {k : Code} (h : StrictMin f k) : pick f = k := by
  by_contra hn
  have hs := h (pick f) hn
  have hm := pick_min f k
  linarith

theorem nearest_one {t : ℝ} (lo : 1/2 < t) (hi : t < 3/2) :
    StrictMin (fun q => (t-value q)^2) 1 := by
  intro q hq
  fin_cases q <;> norm_num [value] at * <;> nlinarith

theorem nearest_two {t : ℝ} (lo : 3/2 < t) (hi : t < 5/2) :
    StrictMin (fun q => (t-value q)^2) 2 := by
  intro q hq
  fin_cases q <;> norm_num [value] at * <;> nlinarith

theorem nearest_three {t : ℝ} (lo : 5/2 < t) :
    StrictMin (fun q => (t-value q)^2) 3 := by
  intro q hq
  fin_cases q <;> norm_num [value] at * <;> nlinarith

theorem loss_identity (w : ℝ) (x y : Samples) (q r : Code) (hg : gram y ≠ 0) :
    qepLoss w x y q - qepLoss w x y r =
    gram y * ((corrected w x y - value q)^2 - (corrected w x y - value r)^2) := by
  unfold qepLoss corrected gram at *
  field_simp
  <;> ring

theorem correction_order (w : ℝ) (x y : Samples) (q r : Code) (hg : 0 < gram y) :
    qepLoss w x y q ≤ qepLoss w x y r ↔
    (corrected w x y - value q)^2 ≤ (corrected w x y - value r)^2 := by
  have hh := loss_identity w x y q r (ne_of_gt hg)
  constructor <;> intro h
  · nlinarith
  · nlinarith

theorem qep_nearest (w : ℝ) (x y : Samples) (hg : 0 < gram y) :
    pick (qepLoss w x y) = nearest (corrected w x y) := by
  simp only [pick, nearest, correction_order w x y _ _ hg]


def baseMsg (a b c : ℝ) : Message :=
  let q₁ := pick (baseLoss a input)
  let x₁ := step (value q₁) input
  let q₂ := pick (baseLoss b x₁)
  let x₂ := step (value q₂) x₁
  let q₃ := pick (baseLoss c x₂)
  (q₁,q₂,q₃)

def qepMsg (a b c : ℝ) : Message :=
  let q₁ := pick (qepLoss a input input)
  let x₁ := step (value q₁) input
  let q₂ := pick (qepLoss b (step a input) x₁)
  let x₂ := step (value q₂) x₁
  let q₃ := pick (qepLoss c (step b (step a input)) x₂)
  (q₁,q₂,q₃)

def decode (m : Message) : Samples :=
  step (value m.2.2) (step (value m.2.1) (step (value m.1) input))
def teacher (a b c : ℝ) : Samples := step c (step b (step a input))

theorem step_input {w : ℝ} (hw : 0 ≤ w) : step w input = (0,w) := by
  simp [step, input, max_eq_left (neg_nonpos.mpr hw), max_eq_right hw]
theorem step_pos {w t : ℝ} (hw : 0 ≤ w) (ht : 0 ≤ t) : step w (0,t) = (0,w*t) := by
  simp [step, max_eq_right (mul_nonneg hw ht)]


structure Cell (a b c : ℝ) : Prop where
  a_lo : 1/2 < a
  a_hi : a < 3/2
  b_lo : 3/2 < b
  b_hi : b < 5/2
  ab_lo : 5/2 < a*b
  ab_hi : a*b < 3
  c_lo : 1/2 < c
  c_hi : c < 3/2
  t_lo : 3/2 < a*b*c
  t_hi : a*b*c < 7/2


theorem base_strict (w : ℝ) (y : Samples) (k : Code)
    (hg : 0 < gram y) (hs : StrictMin (fun q => (w-value q)^2) k) :
    StrictMin (baseLoss w y) k := by
  intro q hq
  have hh := mul_lt_mul_of_pos_left (hs q hq) hg
  dsimp [baseLoss, qepLoss, gram] at *
  nlinarith

theorem corrected_strict (w : ℝ) (x y : Samples) (k : Code)
    (hg : 0 < gram y)
    (hs : StrictMin (fun q => (corrected w x y-value q)^2) k) :
    StrictMin (qepLoss w x y) k := by
  intro q hq
  have hh := loss_identity w x y k q (ne_of_gt hg)
  have hl := mul_lt_mul_of_pos_left (hs q hq) hg
  nlinarith

theorem cell_choices {a b c : ℝ} (h : Cell a b c) :
    StrictMin (baseLoss a input) 1 ∧
    StrictMin (baseLoss b (0,1)) 2 ∧
    StrictMin (baseLoss c (0,2)) 1 ∧
    StrictMin (qepLoss a input input) 1 ∧
    StrictMin (qepLoss b (0,a) (0,1)) 3 ∧
    StrictMin (qepLoss c (0,a*b) (0,3)) 1 := by
  have h1 := base_strict a input 1 (by norm_num [gram, input]) (nearest_one h.a_lo h.a_hi)
  have h2 := base_strict b (0,1) 2 (by norm_num [gram]) (nearest_two h.b_lo h.b_hi)
  have h3 := base_strict c (0,2) 1 (by norm_num [gram]) (nearest_one h.c_lo h.c_hi)
  refine ⟨h1,h2,h3,h1,?_,?_⟩
  · apply corrected_strict b (0,a) (0,1) 3 (by norm_num [gram])
    have he : corrected b (0,a) (0,1) = a*b := by simp [corrected, gram]; ring
    rw [he]
    exact nearest_three h.ab_lo
  · apply corrected_strict c (0,a*b) (0,3) 1 (by norm_num [gram])
    have he : corrected c (0,a*b) (0,3) = a*b*c/3 := by norm_num [corrected, gram]; ring
    rw [he]
    apply nearest_one <;> linarith [h.t_lo, h.t_hi]

theorem cell_messages {a b c : ℝ} (h : Cell a b c) :
    baseMsg a b c = (1,2,1) ∧ qepMsg a b c = (1,3,1) := by
  obtain ⟨h1,h2,h3,hq1,hq2,hq3⟩ := cell_choices h
  have ha : 0 ≤ a := by linarith [h.a_lo]
  have hb : 0 ≤ b := by linarith [h.b_lo]
  have e1 : step a input = (0,a) := step_input ha
  have e2 : step b (step a input) = (0,a*b) := by
    rw [e1, step_pos hb ha]
    congr 1
    ring
  constructor
  · unfold baseMsg
    rw [pick_of_strict h1]
    norm_num [value, step, input]
    rw [pick_of_strict h2]
    norm_num [value, step]
    rw [pick_of_strict h3]
  · have s1 : step (value (1:Code)) input = (0,1) := by norm_num [step,value,input]
    have s3 : step (value (3:Code)) (0,1) = (0,3) := by norm_num [step,value]
    have s2 : step b (0,a) = (0,a*b) := by rw [← e1]; exact e2
    simp only [qepMsg, pick_of_strict hq1, s1, e1, s2, pick_of_strict hq2, s3, pick_of_strict hq3]

theorem cell_teacher {a b c : ℝ} (h : Cell a b c) : teacher a b c = (0,a*b*c) := by
  have ha : 0 ≤ a := by linarith [h.a_lo]
  have hb : 0 ≤ b := by linarith [h.b_lo]
  have hc : 0 ≤ c := by linarith [h.c_lo]
  rw [teacher, step_input ha, step_pos hb ha, step_pos hc (mul_nonneg hb ha)]
  congr 1
  ring

theorem cell_outputs {a b c : ℝ} (h : Cell a b c) :
    decode (baseMsg a b c) = (0,2) ∧ decode (qepMsg a b c) = (0,3) := by
  obtain ⟨hb,hq⟩ := cell_messages h
  rw [hb,hq]
  norm_num [decode, value, step, input]


def input2 (m : Message) : Samples := step (value m.1) input
def input3 (m : Message) : Samples := step (value m.2.1) (input2 m)
def targets (a b c : ℝ) : ℝ × ℝ × ℝ :=
  (corrected a input input,
   corrected b (step a input) (input2 (qepMsg a b c)),
   corrected c (step b (step a input)) (input3 (qepMsg a b c)))

theorem cell_inputs {a b c : ℝ} (h : Cell a b c) :
    input2 (baseMsg a b c) = (0,1) ∧ input3 (baseMsg a b c) = (0,2) ∧
    input2 (qepMsg a b c) = (0,1) ∧ input3 (qepMsg a b c) = (0,3) := by
  obtain ⟨hb,hq⟩ := cell_messages h
  rw [hb,hq]
  norm_num [input2,input3,step,value,input]

theorem cell_targets {a b c : ℝ} (h : Cell a b c) : targets a b c = (a,a*b,a*b*c/3) := by
  obtain ⟨_,_,h2,h3⟩ := cell_inputs h
  have ha : 0 ≤ a := by linarith [h.a_lo]
  have hb : 0 ≤ b := by linarith [h.b_lo]
  unfold targets
  rw [h2,h3,step_input ha,step_pos hb ha]
  norm_num [corrected,gram,input]
  constructor <;> ring

theorem cell_unique_actual {a b c : ℝ} (h : Cell a b c) :
    StrictMin (baseLoss a input) (baseMsg a b c).1 ∧
    StrictMin (baseLoss b (input2 (baseMsg a b c))) (baseMsg a b c).2.1 ∧
    StrictMin (baseLoss c (input3 (baseMsg a b c))) (baseMsg a b c).2.2 ∧
    StrictMin (qepLoss a input input) (qepMsg a b c).1 ∧
    StrictMin (qepLoss b (step a input) (input2 (qepMsg a b c))) (qepMsg a b c).2.1 ∧
    StrictMin (qepLoss c (step b (step a input)) (input3 (qepMsg a b c))) (qepMsg a b c).2.2 := by
  obtain ⟨hb,hq⟩ := cell_messages h
  obtain ⟨hb2,hb3,hq2,hq3⟩ := cell_inputs h
  have ha : 0 ≤ a := by linarith [h.a_lo]
  have hp : 0 ≤ b := by linarith [h.b_lo]
  rw [hb2,hb3,hq2,hq3,hb,hq,step_input ha,step_pos hp ha]
  have hcomm : b*a = a*b := mul_comm b a
  rw [hcomm]
  exact cell_choices h



theorem decode_natural (m : Message) :
    decode m = (0, ((m.1.val*m.2.1.val*m.2.2.val : ℕ) : ℝ)) := by
  have h1 : 0 ≤ value m.1 := Nat.cast_nonneg _
  have h2 : 0 ≤ value m.2.1 := Nat.cast_nonneg _
  have h3 : 0 ≤ value m.2.2 := Nat.cast_nonneg _
  rw [decode,step_input h1,step_pos h2 h1,step_pos h3 (mul_nonneg h2 h1)]
  simp only [value,Nat.cast_mul]
  congr 1
  ring

theorem nearest_nat_two {t : ℝ} (lo : 3/2 ≤ t) (hi : t ≤ 5/2) (n : ℕ) :
    (t-2)^2 ≤ (t-(n:ℝ))^2 := by
  rcases lt_trichotomy n 2 with hn|hn|hn
  · have hn' : (n:ℝ) ≤ 1 := by exact_mod_cast (show n ≤ 1 by omega)
    have hp := mul_nonneg (show 0 ≤ 2-(n:ℝ) by linarith)
      (show 0 ≤ 2*t-(n:ℝ)-2 by linarith)
    nlinarith
  · subst n
    norm_num
  · have hn' : 3 ≤ (n:ℝ) := by exact_mod_cast (show 3 ≤ n by omega)
    have hp := mul_nonneg (show 0 ≤ (n:ℝ)-2 by linarith)
      (show 0 ≤ (n:ℝ)+2-2*t by linarith)
    nlinarith

theorem nearest_nat_three {t : ℝ} (lo : 5/2 ≤ t) (hi : t ≤ 7/2) (n : ℕ) :
    (t-3)^2 ≤ (t-(n:ℝ))^2 := by
  rcases lt_trichotomy n 3 with hn|hn|hn
  · have hn' : (n:ℝ) ≤ 2 := by exact_mod_cast (show n ≤ 2 by omega)
    have hp := mul_nonneg (show 0 ≤ 3-(n:ℝ) by linarith)
      (show 0 ≤ 2*t-(n:ℝ)-3 by linarith)
    nlinarith
  · subst n
    norm_num
  · have hn' : 4 ≤ (n:ℝ) := by exact_mod_cast (show 4 ≤ n by omega)
    have hp := mul_nonneg (show 0 ≤ (n:ℝ)-3 by linarith)
      (show 0 ≤ (n:ℝ)+3-2*t by linarith)
    nlinarith

def baseError (a b c : ℝ) : ℝ := frobError (teacher a b c) (decode (baseMsg a b c))
def qepError (a b c : ℝ) : ℝ := frobError (teacher a b c) (decode (qepMsg a b c))
def baseSquared (a b c : ℝ) : ℝ := sqError (teacher a b c) (decode (baseMsg a b c))
def qepSquared (a b c : ℝ) : ℝ := sqError (teacher a b c) (decode (qepMsg a b c))

theorem cell_errors {a b c : ℝ} (h : Cell a b c) :
    baseError a b c = |a*b*c-2| ∧ qepError a b c = |a*b*c-3| ∧
    baseSquared a b c = (a*b*c-2)^2 ∧ qepSquared a b c = (a*b*c-3)^2 := by
  obtain ⟨hb,hq⟩ := cell_outputs h
  simp [baseError,qepError,baseSquared,qepSquared,cell_teacher h,hb,hq,
    frobError,sqError,Real.sqrt_sq_eq_abs]

theorem cell_global_base {a b c : ℝ} (h : Cell a b c) (ht : a*b*c ≤ 5/2) (m : Message) :
    baseError a b c ≤ frobError (teacher a b c) (decode m) := by
  obtain ⟨hb,_⟩ := cell_outputs h
  unfold baseError frobError
  apply Real.sqrt_le_sqrt
  rw [hb,cell_teacher h,decode_natural]
  simp only [sqError,sub_self,zero_pow (by decide : 2 ≠ 0),zero_add]
  exact nearest_nat_two (le_of_lt h.t_lo) ht _

theorem cell_global_qep {a b c : ℝ} (h : Cell a b c) (ht : 5/2 ≤ a*b*c) (m : Message) :
    qepError a b c ≤ frobError (teacher a b c) (decode m) := by
  obtain ⟨_,hq⟩ := cell_outputs h
  unfold qepError frobError
  apply Real.sqrt_le_sqrt
  rw [hq,cell_teacher h,decode_natural]
  simp only [sqError,sub_self,zero_pow (by decide : 2 ≠ 0),zero_add]
  exact nearest_nat_three ht (le_of_lt h.t_hi) _

structure Box (a b c : ℝ) : Prop where
  a_lo : 27/20 < a
  a_hi : a < 29/20
  b_lo : 39/20 < b
  b_hi : b < 41/20
  c_lo : 7/10 < c
  c_hi : c < 37/50

theorem box_products {a b c : ℝ} (h : Box a b c) :
    1053/400 < a*b ∧ a*b < 1189/400 ∧
    7371/4000 < a*b*c ∧ a*b*c < 43993/20000 := by
  have ha : 0 < a := by linarith [h.a_lo]
  have hb : 0 < b := by linarith [h.b_lo]
  have hc : 0 < c := by linarith [h.c_lo]
  have hablo : 1053/400 < a*b := by
    have h1 := mul_lt_mul_of_pos_right h.a_lo hb
    have h2 := mul_lt_mul_of_pos_left h.b_lo (show (0:ℝ) < 27/20 by norm_num)
    linarith
  have habhi : a*b < 1189/400 := by
    have h1 := mul_lt_mul_of_pos_right h.a_hi hb
    have h2 := mul_lt_mul_of_pos_left h.b_hi (show (0:ℝ) < 29/20 by norm_num)
    linarith
  refine ⟨hablo,habhi,?_,?_⟩
  · have h1 := mul_lt_mul_of_pos_right hablo hc
    have h2 := mul_lt_mul_of_pos_left h.c_lo (show (0:ℝ) < 1053/400 by norm_num)
    linarith
  · have h1 := mul_lt_mul_of_pos_right habhi hc
    have h2 := mul_lt_mul_of_pos_left h.c_hi (show (0:ℝ) < 1189/400 by norm_num)
    linarith

theorem box_cell {a b c : ℝ} (h : Box a b c) : Cell a b c := by
  obtain ⟨hablo,habhi,htlo,hthi⟩ := box_products h
  constructor <;> linarith [h.a_lo,h.a_hi,h.b_lo,h.b_hi,h.c_lo,h.c_hi]

theorem box_worse {a b c : ℝ} (h : Box a b c) : baseError a b c < qepError a b c := by
  have hc := box_cell h
  obtain ⟨hb,hq,_,_⟩ := cell_errors hc
  obtain ⟨_,_,htlo,hthi⟩ := box_products h
  rw [hb,hq]
  rw [abs_of_neg (show a*b*c-3 < 0 by linarith)]
  apply abs_lt.mpr
  constructor <;> linarith

theorem box_oracle {a b c : ℝ} (h : Box a b c) (m : Message) :
    baseError a b c ≤ frobError (teacher a b c) (decode m) := by
  apply cell_global_base (box_cell h) _ m
  linarith [(box_products h).2.2.2]

structure Legal (a b c : ℝ) : Prop where
  weights_and_targets : ∀ w ∈ [a,b,c,(targets a b c).1,(targets a b c).2.1,(targets a b c).2.2],
    0 < w ∧ w < 3
  input_grams : ∀ x ∈ [input,step a input,step b (step a input),
      input2 (baseMsg a b c),input3 (baseMsg a b c),
      input2 (qepMsg a b c),input3 (qepMsg a b c)], 0 < gram x
  selected_nonzero : ∀ w ∈ [value (baseMsg a b c).1,value (baseMsg a b c).2.1,
      value (baseMsg a b c).2.2,value (qepMsg a b c).1,
      value (qepMsg a b c).2.1,value (qepMsg a b c).2.2], w ≠ 0

theorem cell_legal {a b c : ℝ} (h : Cell a b c) : Legal a b c := by
  obtain ⟨hb,hq⟩ := cell_messages h
  obtain ⟨hb2,hb3,hq2,hq3⟩ := cell_inputs h
  have ha : 0 ≤ a := by linarith [h.a_lo]
  have hp : 0 ≤ b := by linarith [h.b_lo]
  have ha' : 0 < a := by linarith [h.a_lo]
  have hp' : 0 < b := by linarith [h.b_lo]
  constructor
  · rw [cell_targets h]
    intro w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl|rfl <;>
      constructor <;> linarith [h.a_lo,h.a_hi,h.b_lo,h.b_hi,h.c_lo,h.c_hi,
        h.ab_lo,h.ab_hi,h.t_lo,h.t_hi]
  · rw [hb2,hb3,hq2,hq3,step_input ha,step_pos hp ha]
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      dsimp [gram,input] <;> positivity
  · rw [hb,hq]
    norm_num [value]



theorem core {a b c : ℝ} (h : Box a b c) :
    baseMsg a b c = (1,2,1) ∧ qepMsg a b c = (1,3,1) ∧
    Legal a b c ∧ baseError a b c < qepError a b c ∧
    (∀ m : Message, baseError a b c ≤ frobError (teacher a b c) (decode m)) := by
  obtain ⟨hb,hq⟩ := cell_messages (box_cell h)
  exact ⟨hb,hq,cell_legal (box_cell h),box_worse h,box_oracle h⟩


theorem witness : Box (7/5) 2 (18/25) := by constructor <;> norm_num

theorem witness_errors :
    baseError (7/5) 2 (18/25) = 2/125 ∧ qepError (7/5) 2 (18/25) = 123/125 := by
  obtain ⟨hb,hq,_,_⟩ := cell_errors (box_cell witness)
  rw [hb,hq]
  norm_num


theorem witness_errors_not_shared :
    value (baseMsg (7/5) 2 (18/25)).2.1 - 2 ≠
    value (qepMsg (7/5) 2 (18/25)).2.1 - (targets (7/5) 2 (18/25)).2.1 := by
  obtain ⟨hb,hq⟩ := cell_messages (box_cell witness)
  rw [hb,hq,cell_targets (box_cell witness)]
  norm_num [value]


structure Boundary (a h c : ℝ) : Prop where
  a_lo : 1/2 < a
  a_hi : a < 3/2
  h_lo : 5/2 < h
  h_hi : h < 3
  b_lo : 3/2 < h/a
  b_hi : h/a < 5/2
  c_lo : 3/(2*h) < c
  c_hi : c < 7/(2*h)

theorem boundary_cell {a h c : ℝ} (p : Boundary a h c) : Cell a (h/a) c := by
  have ha : 0 < a := by linarith [p.a_lo]
  have hh : 0 < h := by linarith [p.h_lo]
  have hab : a*(h/a) = h := by field_simp
  have hc : 0 < c := lt_trans (div_pos (by norm_num) (by positivity)) p.c_lo
  have hlow := (div_lt_iff₀ (show 0 < 2*h by positivity)).mp p.c_lo
  have hhi := (lt_div_iff₀ (show 0 < 2*h by positivity)).mp p.c_hi
  have hc1 := mul_lt_mul_of_pos_right p.h_hi hc
  have hc2 := mul_lt_mul_of_pos_right p.h_lo hc
  constructor
  · exact p.a_lo
  · exact p.a_hi
  · exact p.b_lo
  · exact p.b_hi
  · rw [hab]; exact p.h_lo
  · rw [hab]; exact p.h_hi
  · nlinarith
  · nlinarith
  · rw [hab]; nlinarith
  · rw [hab]; nlinarith

theorem cell_sharp {a b c : ℝ} (p : Cell a b c) :
    qepSquared a b c - baseSquared a b c = 5-2*(a*b*c) ∧
    (baseError a b c < qepError a b c ↔ a*b*c < 5/2) ∧
    (baseError a b c = qepError a b c ↔ a*b*c = 5/2) ∧
    (qepError a b c < baseError a b c ↔ 5/2 < a*b*c) := by
  obtain ⟨hb,hq,hbs,hqs⟩ := cell_errors p
  rw [hb,hq,hbs,hqs]
  refine ⟨by ring,?_,?_,?_⟩
  · rw [← sq_lt_sq]
    constructor <;> intro hh <;> nlinarith
  · rw [← sq_eq_sq_iff_abs_eq_abs]
    constructor <;> intro hh <;> nlinarith
  · rw [← sq_lt_sq]
    constructor <;> intro hh <;> nlinarith


theorem boundary_sharp {a h c : ℝ} (p : Boundary a h c) :
    baseMsg a (h/a) c = (1,2,1) ∧ qepMsg a (h/a) c = (1,3,1) ∧
    Legal a (h/a) c ∧
    qepSquared a (h/a) c - baseSquared a (h/a) c = 5-2*(h*c) ∧
    (baseError a (h/a) c < qepError a (h/a) c ↔ h*c < 5/2) ∧
    (baseError a (h/a) c = qepError a (h/a) c ↔ h*c = 5/2) ∧
    (qepError a (h/a) c < baseError a (h/a) c ↔ 5/2 < h*c) := by
  have hc := boundary_cell p
  obtain ⟨hb,hq⟩ := cell_messages hc
  have hs := cell_sharp hc
  have ha : a ≠ 0 := ne_of_gt (by linarith [p.a_lo] : 0 < a)
  have hab : a*(h/a) = h := by field_simp
  rw [hab] at hs
  exact ⟨hb,hq,cell_legal hc,hs⟩

theorem boundary_oracles {a h c : ℝ} (p : Boundary a h c) :
    (h*c ≤ 5/2 → ∀ m : Message,
      baseError a (h/a) c ≤ frobError (teacher a (h/a) c) (decode m)) ∧
    (5/2 ≤ h*c → ∀ m : Message,
      qepError a (h/a) c ≤ frobError (teacher a (h/a) c) (decode m)) := by
  have hc := boundary_cell p
  have ha : a ≠ 0 := ne_of_gt (by linarith [p.a_lo] : 0 < a)
  have hab : a*(h/a) = h := by field_simp
  constructor
  · intro ht m
    apply cell_global_base hc _ m
    rwa [hab]
  · intro ht m
    apply cell_global_qep hc _ m
    rwa [hab]


theorem benefit_condition : Boundary (7/5) (14/5) (11/10) := by constructor <;> norm_num

theorem benefit_prediction :
    baseMsg (7/5) 2 (11/10) = (1,2,1) ∧ qepMsg (7/5) 2 (11/10) = (1,3,1) ∧
    baseError (7/5) 2 (11/10) = 27/25 ∧ qepError (7/5) 2 (11/10) = 2/25 := by
  have hc : Cell (7/5) 2 (11/10) := by
    convert boundary_cell benefit_condition using 1 <;> norm_num
  obtain ⟨hb,hq⟩ := cell_messages hc
  obtain ⟨he1,he2,_,_⟩ := cell_errors hc
  rw [he1,he2]
  exact ⟨hb,hq,by norm_num,by norm_num⟩



def noPropagationSecond (a b c : ℝ) : Message :=
  let q₁ := pick (qepLoss a input input)
  let x₁ := step (value q₁) input
  let q₂ := pick (qepLoss b x₁ x₁)
  let x₂ := step (value q₂) x₁
  let q₃ := pick (qepLoss c (step b (step a input)) x₂)
  (q₁,q₂,q₃)

theorem control_equal :
    frobError (teacher (7/5) 2 (18/25)) (decode (noPropagationSecond (7/5) 2 (18/25))) =
    baseError (7/5) 2 (18/25) := by
  have hm : noPropagationSecond (7/5) 2 (18/25) = (1,2,1) := by
    norm_num [noPropagationSecond,pick,qepLoss,input,step,value]
  have hb := (cell_messages (box_cell witness)).1
  unfold baseError
  rw [hm,hb]



theorem cell_base_fp_unique {a b c : ℝ} (h : Cell a b c) :
    StrictMin (baseLoss a input) 1 ∧
    StrictMin (baseLoss b (step a input)) 2 ∧
    StrictMin (baseLoss c (step b (step a input))) 1 := by
  have ha : 0 < a := by linarith [h.a_lo]
  have hb : 0 < b := by linarith [h.b_lo]
  refine ⟨(cell_choices h).1,?_,?_⟩
  · apply base_strict _ _ _ _ (nearest_two h.b_lo h.b_hi)
    rw [step_input (le_of_lt ha)]
    dsimp [gram]
    positivity
  · apply base_strict _ _ _ _ (nearest_one h.c_lo h.c_hi)
    rw [step_input (le_of_lt ha),step_pos (le_of_lt hb) (le_of_lt ha)]
    dsimp [gram]
    positivity

end
end QepInterior
