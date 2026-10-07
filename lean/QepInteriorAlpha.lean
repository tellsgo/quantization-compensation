import QepInterior
import Mathlib.Tactic.SplitIfs



set_option autoImplicit false
namespace QepInterior
noncomputable section

def correctedAlpha (alpha w : ℝ) (x y : Samples) : ℝ :=
  w + alpha * (corrected w x y - w)

def qepMsgAlpha2 (alpha a b c : ℝ) : Message :=
  let q₁ := pick (qepLoss a input input)
  let x₁ := step (value q₁) input
  let q₂ := pick (baseLoss (correctedAlpha alpha b (step a input) x₁) x₁)
  let x₂ := step (value q₂) x₁
  let q₃ := pick (qepLoss c (step b (step a input)) x₂)
  (q₁,q₂,q₃)

theorem alpha_half_message :
    qepMsgAlpha2 (1/2) (7/5) 2 (18/25) = (1,2,1) := by
  norm_num [qepMsgAlpha2,correctedAlpha,corrected,gram,pick,baseLoss,qepLoss,step,value,input]

theorem alpha_three_quarters_message :
    qepMsgAlpha2 (3/4) (7/5) 2 (18/25) = (1,3,1) := by
  norm_num [qepMsgAlpha2,correctedAlpha,corrected,gram,pick,baseLoss,qepLoss,step,value,input]

theorem alpha_numeric_errors :
    sqError (teacher (7/5) 2 (18/25))
      (decode (qepMsgAlpha2 (1/2) (7/5) 2 (18/25))) = 4/15625 ∧
    sqError (teacher (7/5) 2 (18/25))
      (decode (qepMsgAlpha2 (3/4) (7/5) 2 (18/25))) = 15129/15625 := by
  rw [alpha_half_message,alpha_three_quarters_message]
  norm_num [sqError,teacher,decode,step,value,input]

theorem alpha_second_target (alpha : ℝ) :
    correctedAlpha alpha 2 (step (7/5) input) (step 1 input) = 2+4*alpha/5 := by
  norm_num [correctedAlpha,corrected,step,input,gram]
  ring

theorem alpha_switch_order (alpha : ℝ) :
    baseLoss (correctedAlpha alpha 2 (step (7/5) input) (step 1 input))
      (step 1 input) 2 ≤
    baseLoss (correctedAlpha alpha 2 (step (7/5) input) (step 1 input))
      (step 1 input) 3 ↔ alpha ≤ 5/8 := by
  rw [alpha_second_target]
  norm_num [baseLoss,qepLoss,step,input,value]
  constructor <;> intro h <;> nlinarith

theorem alpha_second_pick {alpha : ℝ} (h0 : 0 ≤ alpha) (h1 : alpha ≤ 1) :
    pick (baseLoss (correctedAlpha alpha 2 (step (7/5) input) (step 1 input))
      (step 1 input)) = if alpha ≤ 5/8 then 2 else 3 := by
  rw [alpha_second_target]
  norm_num [pick,baseLoss,qepLoss,step,input,value]
  split_ifs <;> norm_num at * <;> nlinarith

theorem alpha_messages_piecewise {alpha : ℝ} (h0 : 0 ≤ alpha) (h1 : alpha ≤ 1) :
    qepMsgAlpha2 alpha (7/5) 2 (18/25) =
      if alpha ≤ 5/8 then (1,2,1) else (1,3,1) := by
  have hfirst : pick (qepLoss (7/5) input input) = 1 := by
    norm_num [pick,qepLoss,input,value]
  have hsecond := alpha_second_pick h0 h1
  norm_num [step,input] at hsecond
  unfold qepMsgAlpha2
  rw [hfirst]
  norm_num [value,step,input]
  rw [hsecond]
  split_ifs <;> norm_num [pick,qepLoss,step,value,input]

theorem alpha_switch_tie :
    qepMsgAlpha2 (5/8) (7/5) 2 (18/25) = (1,2,1) := by
  norm_num [qepMsgAlpha2,correctedAlpha,corrected,gram,pick,baseLoss,qepLoss,step,value,input]

end
end QepInterior
