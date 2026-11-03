import VersoManual.Literate

open Verso.Genre Manual VersoLiterate Verso.Code.External

namespace MorewManual.ExampleSource

/-- Render source examples with their printed results. -/
scoped instance : LoadLiterate Manual :=
  { (inferInstance : LoadLiterate Manual) with
    block := fun _goI goB => fun
      | .highlighted hl, _ =>
        let output := (allInfo hl).filterMap fun (message, _) =>
          if message.severity == .info then
            some (ExternalCode.leanOutputBlock message)
          else none
        .concat (#[ExternalCode.leanBlock hl {}] ++ output)
      | .data .., content => .concat (content.map goB) }

private partial def spaceBreaks : MD4Lean.Text → MD4Lean.Text
  | .softbr _ | .br _ => .normal " "
  | .em xs => .em (xs.map spaceBreaks)
  | .strong xs => .strong (xs.map spaceBreaks)
  | .u xs => .u (xs.map spaceBreaks)
  | .a href title auto xs => .a href title auto (xs.map spaceBreaks)
  | .img src title xs => .img src title (xs.map spaceBreaks)
  | .del xs => .del (xs.map spaceBreaks)
  | .wikiLink target xs => .wikiLink target (xs.map spaceBreaks)
  | other => other

private partial def normalizeBlock : MD4Lean.Block → MD4Lean.Block
  | .p xs => .p (xs.map spaceBreaks)
  | .header level xs => .header level (xs.map spaceBreaks)
  | .ul tight mark items =>
    .ul tight mark (items.map fun item => { item with contents := item.contents.map normalizeBlock })
  | .ol tight start mark items =>
    .ol tight start mark (items.map fun item => { item with contents := item.contents.map normalizeBlock })
  | .blockquote blocks => .blockquote (blocks.map normalizeBlock)
  | .table head body => .table (head.map (·.map spaceBreaks)) (body.map (·.map (·.map spaceBreaks)))
  | other => other

-- Verso 4.33.0 drops Markdown line breaks; each page already supplies its module title.
private def normalizeModule (source : LitMod) : LitMod := Id.run do
  let mut firstModuleDoc := true
  let mut contents := #[]
  for item in source.contents do
    let mut code := #[]
    for part in item.code do
      let normalized ← match part with
        | .markdownModDoc doc => do
          let mut blocks := doc.blocks.map normalizeBlock
          if firstModuleDoc then
            if let some (.header 1 _) := blocks[0]? then
              blocks := blocks.extract 1
          firstModuleDoc := false
          pure (.markdownModDoc { blocks })
        | .markdown indent name doc =>
          pure (.markdown indent name { blocks := doc.blocks.map normalizeBlock })
        | other => pure other
      code := code.push normalized
    contents := contents.push { item with code }
  return { source with contents }

private def renderExample (json title : String) : Verso.Doc.VersoDoc Manual :=
  modToPage! (normalizeModule (loadJsonString! json)) #[.text title] title none

open Lean Lean.Elab Term Verso.Doc.Elab Verso.ArgParse
open Lean.Doc.Syntax

private structure ExampleConfig where
  modName : Ident
  title : StrLit

private meta instance [Monad m] [MonadError m] [MonadLiftT CoreM m] : FromArgs ExampleConfig m where
  fromArgs := ExampleConfig.mk <$> .positional' `name <*> .positional' `title

@[part_command Lean.Doc.Syntax.command]
meta def includeExample : PartCommand
  | `(block|command{includeExample $args*}) => do
    let { modName, title } ← parseThe ExampleConfig (← parseArgs args)
    let json ← loadModuleJson "." modName.getId.toString
    let name ← mkFreshUserName (modName.getId ++ `examplePage)
    let value ← elabTerm (← ``(renderExample $(quote json) $(quote title.getString))) none
    withOptions (Lean.Compiler.LCNF.compiler.extract_closed.set · false) do
      addAndCompile <| .defnDecl {
        name, levelParams := [], type := ← Lean.Meta.inferType value, value,
        hints := .regular 0, safety := .safe
      }
    PartElabM.addPart (.included (mkIdentFrom modName name))
  | _ => Lean.Elab.throwUnsupportedSyntax

end MorewManual.ExampleSource
