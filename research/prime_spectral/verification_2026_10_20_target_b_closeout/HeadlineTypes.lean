import Reinmann.XiFinitePFCertified
example : Reinmann.ZetaNoLowStripZero (141/10) := Reinmann.XiRectangle.zetaNoLowStripZero
example : Reinmann.FinitePF Reinmann.XiMomentCoeff 43 := Reinmann.XiFinitePFCertified.finitePF43
example (h : Reinmann.QuasiRiemannHypothesisSevenEighths) :
    Reinmann.FinitePF Reinmann.XiMomentCoeff 58 := Reinmann.XiFinitePFCertified.finitePF58 h
#print axioms Reinmann.XiRectangle.rectangle_nonzero
#print axioms Reinmann.XiRectangle.zetaNoLowStripZero
#print axioms Reinmann.XiHadamardProduct.katkovaSectorBridge
#print axioms Reinmann.XiFinitePFCertified.finitePF43
#print axioms Reinmann.XiFinitePFCertified.finitePF58
