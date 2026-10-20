import Reinmann.XiFinitePFCertified

example : Reinmann.FinitePF Reinmann.XiMomentCoeff 43 :=
  Reinmann.XiFinitePFCertified.finitePF43

example (hq : Reinmann.QuasiRiemannHypothesisSevenEighths) :
    Reinmann.FinitePF Reinmann.XiMomentCoeff 58 :=
  Reinmann.XiFinitePFCertified.finitePF58 hq

example (m : ℕ) (hm : 0 < m) : Reinmann.KatkovaSectorBridge m :=
  Reinmann.XiHadamardProduct.katkovaSectorBridge m hm
