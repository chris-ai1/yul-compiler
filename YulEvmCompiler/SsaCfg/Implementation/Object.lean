import YulEvmCompiler.ObjectCompile
import YulEvmCompiler.SsaCfg.Implementation.Compile
set_option warningAsError true
/-!
# YulEvmCompiler.SsaCfg.Implementation.Object

The SSA backend's **object path**: the classic recursive layout fixpoint
(`planObjectWith`/`compileResolvedObjectWith`, see `ObjectCompile.lean`)
driven by `compileViaSsa` as the per-code-block compiler. Deploy and runtime
code blocks of the object tree compile through the SSA dialect; layout
resolution, the `STOP` seam, child embedding, and data segments are exactly
the classic machinery.
-/

namespace YulEvmCompiler.SsaCfg

open YulSemantics (Object)
open YulSemantics.EVM (Op)

/-- Compile a full object tree with the SSA backend on every code block. -/
def compileObjectViaSsa (o : Object Op) : Option YulSemantics.EVM.Layout :=
  compileResolvedObjectWith compileViaSsa o

/-- **PROTOTYPE, UNPROVEN.** SSA object compiler with the Asm window scheduler
applied to every code block. -/
def compileObjectViaSsaScheduled (o : Object Op) : Option YulSemantics.EVM.Layout :=
  compileResolvedObjectWith compileViaSsaScheduled o

end YulEvmCompiler.SsaCfg
