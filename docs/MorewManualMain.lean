import VersoManual
import MorewManual

open Verso.Genre Manual

def main := manualMain (%doc MorewManual) (config := {
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  extraCss := { .mk "
    .content-wrapper pre,
    .content-wrapper code.hl.lean.block {
      background-color: #f6f8fa;
      padding: 0.75rem 1rem;
      border-radius: 0.375rem;
    }

    .content-wrapper code:not(.block):not(pre code) {
      background-color: #f6f8fa;
      padding: 0.1em 0.3em;
      border-radius: 0.25rem;
    }
  " }
})
