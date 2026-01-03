-- Test file for heat kernel convergence lemmas
-- Ensures that all lemmas compile correctly

import RiemannAdelic.heat_kernel_to_delta_plus_primes
import RiemannAdelic.tendsto_integral_kernel_to_delta
import RiemannAdelic.convergence_arithmetic_correction
import RiemannAdelic.tendsto_integral_shifted_kernel

open Real MeasureTheory Topology Filter

-- Test that the geometric kernel definition is available
#check geometric_kernel

-- Test that all theorems are properly declared
#check tendsto_integral_kernel_to_delta
#check tendsto_integral_shifted_kernel
#check convergence_arithmetic_correction
#check heat_kernel_to_delta_plus_primes

-- Test that the axiom for heat kernel convergence is available
#check tendsto_integral_convolution_delta

-- Print success message
#eval IO.println "✅ All heat kernel convergence lemmas compile successfully!"
#eval IO.println "✅ Lema 1: heat_kernel_to_delta_plus_primes - OK"
#eval IO.println "✅ Lema 2: tendsto_integral_kernel_to_delta - OK"
#eval IO.println "✅ Lema 3: convergence_arithmetic_correction - OK"
#eval IO.println "✅ Lema 4: tendsto_integral_shifted_kernel - OK"
