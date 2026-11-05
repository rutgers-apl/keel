import Vbcf.Replay
import Vbcf.Rules.Bool
import Vbcf.Rules.Clause
import Vbcf.Rules.Aci
import Vbcf.Rules.Eval
import Vbcf.Rules.Poly
import Vbcf.Rules.Rewrite
import Vbcf.Rules.Bitblast

/-! # Vbcf: the whole program -/

namespace Vbcf
open EmbC

def prog : Prog :=
  { structs := [ckS]
    fns := coreFns ++ basicFns ++ boolFns ++ clauseFns ++ aciFns ++ evalFns ++ polyFns
      ++ rewriteFns ++ bitblastFns ++ replayFns
    consts := rewriteConsts }

end Vbcf
