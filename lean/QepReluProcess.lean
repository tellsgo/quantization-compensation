import QepFiniteDitherLaw
import QepReluIntegrals
set_option maxHeartbeats 1000000
open MeasureTheory Set Function
open QepFiniteDitherLaw QepReluIntegrals
namespace QepReluProcess
noncomputable section

def quantize (t d : ℝ) : ℝ := grid (t+d)-d
def first (d : ℝ) : ℝ := relu (quantize 1 d)

def target (d : ℝ) : ℝ := -(1/4:ℝ)+(-(1/4:ℝ))*(1-first d)*first d/(first d*first d)
def qbase (d : ℝ×ℝ) : ℝ := quantize (-(1/4)) d.2
def qqep (d : ℝ×ℝ) : ℝ := quantize (target d.1) d.2
def actualBase (d : ℝ×ℝ) : ℝ := relu (qbase d*first d.1)
def actualQep (d : ℝ×ℝ) : ℝ := relu (qqep d*first d.1)
def firstError (d : ℝ) : ℝ := quantize 1 d-1
def errors (qep : Bool) (d : ℝ×ℝ) : ℝ×ℝ :=
  (firstError d.1, quantize (if qep then target d.1 else -(1/4)) d.2-
    (if qep then target d.1 else -(1/4)))
def baseOutput (e : ℝ×ℝ) : ℝ := relu ((e.2-1/4)*(1+e.1))
def qepOutput (e : ℝ×ℝ) : ℝ := relu (e.2*(1+e.1)-1/4)

theorem first_bounds (d : ℝ) : (1/2:ℝ) < quantize 1 d ∧ quantize 1 d ≤ 3/2 := by
  have hl := sub_half_lt_round (1+d)
  have hh := round_le_add_half (1+d)
  dsimp [quantize,grid]
  constructor <;> linarith

theorem first_eq (d : ℝ) : first d=1+firstError d := by
  rw [first, relu, max_eq_right (by linarith [(first_bounds d).1])]
  unfold firstError; ring

theorem first_positive (d : ℝ) : 0 < first d := by
  rw [first_eq]; unfold firstError; linarith [(first_bounds d).1]

theorem input_gram_positive (d : ℝ) : 0 < first d*first d := mul_pos (first_positive d) (first_positive d)

theorem target_eq (d : ℝ) : target d= -1/(4*first d) := by
  have hn := ne_of_gt (first_positive d)
  unfold target
  field_simp [hn]
  ring

theorem first_error_measurable : Measurable firstError := by
  unfold firstError quantize
  exact ((grid_measurable.comp (measurable_const.add measurable_id)).sub measurable_id).sub measurable_const

theorem target_measurable : Measurable target := by
  have hf : Measurable first := by
    have heq : first = fun d => 1+firstError d := funext first_eq
    rw [heq]
    exact measurable_const.add first_error_measurable
  unfold target
  exact ((measurable_const.mul (measurable_const.sub hf)).mul hf).div (hf.mul hf) |>.const_add _

theorem actual_innovation_law (qep : Bool) :
    MeasurePreserving (errors qep) (noise.prod noise) (noise.prod noise) := by
  have hfirst : MeasurePreserving firstError noise noise :=
    ⟨first_error_measurable,infinite_dither_law 1⟩
  let t : ℝ→ℝ := fun d => if qep then target d else -(1/4)
  have ht : Measurable t := by cases qep <;> simp [t, target_measurable]
  have htp : Measurable (fun p : ℝ×ℝ => t p.1) := ht.comp measurable_fst
  have hm : Measurable (uncurry (fun d₁ d₂ => quantize (t d₁) d₂-t d₁)) := by
    change Measurable (fun p : ℝ×ℝ => grid (t p.1+p.2)-p.2-t p.1)
    exact ((grid_measurable.comp (htp.add measurable_snd)).sub measurable_snd).sub htp
  exact hfirst.skew_product hm (Filter.Eventually.of_forall fun d => infinite_dither_law (t d))

theorem actual_base_identity (d : ℝ×ℝ) : actualBase d=baseOutput (errors false d) := by
  unfold actualBase baseOutput qbase errors
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [first_eq]
  congr 1
  ring

theorem actual_qep_identity (d : ℝ×ℝ) : actualQep d=qepOutput (errors true d) := by
  unfold actualQep qepOutput qqep errors
  simp only [↓reduceIte]
  rw [← first_eq, target_eq]
  congr 1
  have hn := ne_of_gt (first_positive d.1)
  field_simp [hn]
  ring

end
end QepReluProcess
