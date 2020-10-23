import basic 

def norm_sq (z : ℂ) : ℝ := z.re*z.re + z.im*z.im

def inv (z : ℂ) : ℂ := z * (norm_sq z)⁻¹