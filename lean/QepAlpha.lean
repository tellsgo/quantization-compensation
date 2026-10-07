import QepSharedE








namespace QepAlpha
noncomputable section
open QepSharedE
set_option maxHeartbeats 2000000

def run (e a : ℝ) : Trace := qepTrace fixed (noise e) 1 a
def error (e a : ℝ) : ℝ := terminalError fixed (run e a)


theorem output_closed {e : ℝ} (he : 0 < e) (a : ℝ) :
    (run e a).output = 1-a*e-e^2 := by
  have hd : 1+e ≠ 0 := by linarith
  have hf : corrected 1 1 1 1 = 1 := by norm_num [corrected, gram]
  simp only [run, qepTrace, fixed, noise, teacher2, activation, mul_one, hf]
  unfold corrected gram
  field_simp [hd]
  <;> ring


theorem positive_input_gram {e : ℝ} (he : 0 < e) (a : ℝ) :
    0 < gram (run e a).input1 ∧ 0 < gram (run e a).input2 := by
  have hf : corrected 1 1 1 1 = 1 := by norm_num [corrected, gram]
  simp only [run, qepTrace, fixed, noise, activation, mul_one, hf]
  constructor
  · norm_num [gram]
  · unfold gram
    positivity

theorem error_closed {e a : ℝ} (he : 0 < e) (ha : 0 ≤ a) :
    error e a = a*e+e^2 := by
  have hout := output_closed he a
  unfold error terminalError
  rw [hout]
  have hid : (1:ℝ)-(1-a*e-e^2) = a*e+e^2 := by ring
  simp only [teacherOutput, teacher2, fixed, activation, mul_one, hid]
  exact abs_of_nonneg (by positivity)


theorem terminal_strict_increase {e a b : ℝ}
    (he : 0 < e) (ha : 0 ≤ a) (hab : a < b) :
    error e a < error e b := by
  have hb : 0 ≤ b := by linarith
  rw [error_closed he ha, error_closed he hb]
  have h := mul_lt_mul_of_pos_right hab he
  linarith

theorem squared_terminal_strict_increase {e a b : ℝ}
    (he : 0 < e) (ha : 0 ≤ a) (hab : a < b) :
    (error e a)^2 < (error e b)^2 := by
  have hb : 0 ≤ b := by linarith
  have h := terminal_strict_increase he ha hab
  have hnon : 0 ≤ error e a := by rw [error_closed he ha]; positivity
  nlinarith [sq_nonneg (error e b-error e a)]


theorem not_terminal_antitone {e : ℝ} (he : 0 < e) :
    ¬ (∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → error e b ≤ error e a) := by
  intro h
  have hbad := h 0 1 (by norm_num) (by norm_num) (by norm_num)
  have hgood := terminal_strict_increase (e:=e) (a:=0) (b:=1) he
    (by norm_num) (by norm_num)
  linarith


def triangleBound (e a : ℝ) : ℝ := (2-a)*e+e^2

theorem bound_decreases {e a b : ℝ} (he : 0 < e) (hab : a < b) :
    triangleBound e b < triangleBound e a := by
  unfold triangleBound
  have h := mul_lt_mul_of_pos_right hab he
  nlinarith

theorem bound_still_valid {e a : ℝ} (he : 0 < e) (ha : 0 ≤ a) (hu : a ≤ 1) :
    error e a ≤ triangleBound e a := by
  rw [error_closed he ha]
  unfold triangleBound
  have h := mul_nonneg (sub_nonneg.mpr hu) (le_of_lt he)
  nlinarith

end
end QepAlpha
