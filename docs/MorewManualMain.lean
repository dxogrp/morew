import VersoManual
import MorewManual

open Verso.Genre Manual

private def config : RenderConfig := {
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 3
  extraCss := { .mk "
    .content-wrapper pre,
    .content-wrapper code.hl.lean.block {
      background-color: #f6f8fa;
      padding: 0.75rem 1rem;
      border-radius: 0.375rem;
    }

    .content-wrapper code:not(.block):not(.math):not(pre code) {
      background-color: #f6f8fa;
      padding: 0.1em 0.3em;
      border-radius: 0.25rem;
    }

    table.tabular[id^='functions-'] {
      display: block;
      max-width: 100%;
      overflow-x: auto;
    }

    table.tabular[id^='functions-'] .katex {
      white-space: nowrap;
    }
  " }
}

def main (args : List String) : IO UInt32 := do
  let result ← IO.Process.output { cmd := "git", args := #["rev-parse", "HEAD"] }
  if result.exitCode != 0 then
    throw <| IO.userError "Cannot read the documentation source commit."
  let commit := result.stdout.trimAscii.toString
  let sourceUrl := s!"https://github.com/dxogrp/morew/tree/{commit}"
  manualMain (%doc MorewManual) (options := args) (config := { config with
    sourceLink := some sourceUrl
  })
