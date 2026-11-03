import VersoManual
import MorewManual

open Verso.Genre Manual

def main := manualMain (%doc MorewManual) (config := {
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
})
