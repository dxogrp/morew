import VersoManual

open Verso.Genre Manual
open Verso.Doc.Elab Verso.ArgParse Lean

namespace MorewManual.FunctionSymbols

inline_extension propertySymbol (label path : String) where
  data := toJson (label, path)
  traverse _ _ _ := pure none
  toTeX := some fun go _ _ content => content.mapM go
  toHtml := some fun go _ data content => open Verso.Output.Html in do
    let .ok (label, path) := fromJson? (α := String × String) data
      | Verso.reportError "Invalid function symbol"; return .empty
    let symbol ← if path.isEmpty then Verso.Output.Html.seq <$> content.mapM go else
      pure {{<svg viewBox="0 0 24 16" aria-hidden="true">
        <path d={{path}}></path>
      </svg>}}
    pure {{<span class="function-symbol" role="img" aria-label={{label}} title={{label}}>
      {{symbol}}
    </span>}}
  extraCss := [r#"
.function-symbol {
  display: inline-flex;
  align-items: center;
  vertical-align: -0.1em;
}
.function-symbol svg {
  width: 1.3em;
  height: 1em;
  fill: none;
  stroke: currentColor;
  stroke-width: 1.8;
  stroke-linecap: round;
}
"#]

private structure SymbolConfig where
  name : Ident

private meta instance [Monad m] [MonadError m] [MonadLiftT CoreM m] : FromArgs SymbolConfig m where
  fromArgs := SymbolConfig.mk <$> .positional' `name

/-- A function-property symbol with a hover label and accessible name. -/
@[role]
meta def functionSymbol : RoleExpanderOf SymbolConfig
  | ⟨name⟩, _ => do
    let (label, path, text) ← match name.getId with
      | `convex => pure ("Convex", "M 2 2 Q 12 26 22 2", "Convex")
      | `concave => pure ("Concave", "M 2 14 Q 12 -10 22 14", "Concave")
      | `affine => pure ("Affine", "M 2 14 L 22 2", "Affine")
      | `increasing => pure ("Nondecreasing", "", "↗")
      | `decreasing => pure ("Nonincreasing", "", "↘")
      | `neither => pure ("Neither convex nor concave", "", "—")
      | `notMonotone => pure ("Neither nondecreasing nor nonincreasing", "", "—")
      | _ => throwErrorAt name "Unknown function property '{name.getId}'"
    ``(Verso.Doc.Inline.other (propertySymbol $(quote label) $(quote path))
      #[Verso.Doc.Inline.text $(quote text)])

end MorewManual.FunctionSymbols
