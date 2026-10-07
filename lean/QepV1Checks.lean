import QepV1DomainBound

set_option autoImplicit false
namespace QepV1



theorem check_shared_error_required :
    |(scalarTarget 1 1 1 (1/2)+1)*1-(1+0)*1| > (0:ℝ) := by
  norm_num [scalarTarget]


theorem check_gram_legality_required :
    scalarTarget 1 1 0 1*0 ≠ (1*0+1*1*(1-0) : ℝ) := by
  norm_num [scalarTarget]


theorem check_error_transport_required :
    (scalarTarget 1 3 2 (1/2)+1)*2-(1+1)*1 ≠
      (1*(2-1)*(1-(1/2))+ (1/2)*1*(3-1) : ℝ) := by
  norm_num [scalarTarget]


theorem check_coefficient_interval_required : |(1:ℝ)-3*1| > |(1:ℝ)| := by norm_num

end QepV1
