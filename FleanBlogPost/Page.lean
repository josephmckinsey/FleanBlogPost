import Std.Data.HashMap
import Std.Data.HashSet

import SubVerso.Highlighting
import SubVerso.Examples

import Verso.Doc
import Verso.Doc.Html
import Verso.Method
import VersoBlog.LexedText
import Verso.Code
import Verso.Doc.ArgParse
import Verso.Doc.Lsp
import Verso.Doc.Suggestion
import Verso.Hover

open Std (HashSet HashMap)

open Verso Doc Output Html Code Highlighted.WebAssets
open SubVerso.Highlighting

abbrev LexedText.Highlighted := Array (Option String × String)

structure LexedText where
  name : String
  content : LexedText.Highlighted
deriving Repr, Inhabited, BEq, DecidableEq

open Lean in
open Syntax (mkCApp) in
instance : Quote LexedText where
  quote text :=
    mkCApp ``LexedText.mk #[quote text.name, quote text.content]

namespace LexedText

open Lean Parser

open Verso.Parser (ignoreFn)

-- In the absence of a proper regexp engine, abuse ParserFn here
structure Highlighter where
  name : String
  lexer : ParserFn
  tokenClass : Syntax → Option String

def highlight (hl : Highlighter) (str : String) : IO LexedText := do
  let mut out : Highlighted := #[]
  let mut unHl : Option String := none
  let env ← mkEmptyEnvironment
  let ictx := mkInputContext str "<input>"
  let pmctx : ParserModuleContext := {env := env, options := .empty}
  let mut s := mkParserState str
  repeat
    if str.atEnd s.pos then break
    let s' := hl.lexer.run ictx pmctx {} s
    if s'.hasError then
      let c := str.get! s.pos
      unHl := unHl.getD "" |>.push c
      s := {s with pos := s.pos + c}
    else
      let stk := s'.stxStack.extract 0 s'.stxStack.size
      if stk.size ≠ 1 then
        unHl := unHl.getD "" ++ str.extract s.pos s'.pos
        s := s'.restore 0 s'.pos
      else
        let stx := stk[0]!
        match hl.tokenClass stx with
        | none => unHl := unHl.getD "" ++ str.extract s.pos s'.pos
        | some tok =>
          if let some ws := unHl then
            out := out.push (none, ws)
            unHl := none
          out := out.push (some tok, str.extract s.pos s'.pos)
        s := s'.restore 0 s'.pos
  pure ⟨hl.name, out⟩

def token (kind : Name) (p : ParserFn) : ParserFn :=
  nodeFn kind <| ignoreFn p

end LexedText

inductive BlockExt where
  | highlightedCode (contextName : Lean.Name) (highlighted : Highlighted)
  | lexedText (content : LexedText)
  | htmlDiv (classes : String)
  | htmlWrapper (tag : String) (attributes : Array (String × String))
  | htmlDetails (classes : String)
  | blob (html : Html)

inductive InlineExt where
  | highlightedCode (contextName : Lean.Name) (highlighted : Highlighted)
  | customHighlight (highlighted : Highlighted)
  | label (name : Lean.Name)
  | ref (name : Lean.Name)
  | htmlSpan (classes : String)
  | blob (html : Html)
deriving Repr

structure Config where
  destination : System.FilePath := "./_site"
  logError : String → IO Unit
deriving Inhabited

class MonadConfig (m : Type → Type u) where
  currentConfig : m Config

export MonadConfig (currentConfig)

def logError [Monad m] [MonadConfig m] [MonadLift IO m] (message : String) : m Unit := do
  (← currentConfig).logError message

structure TraverseContext where
  path : List String := {}
  config : Config

deriving instance Ord for List -- TODO - upstream?

structure Target where
  path : List String
  htmlId : String
deriving BEq

structure TraverseState where
  usedIds : Lean.RBMap (List String) (HashSet String) compare := {}
  targets : Lean.NameMap Target := {}
  scripts : HashSet String := {}
  stylesheets : HashSet String := {}
  jsFiles : Array (String × String) := #[]
  cssFiles : Array (String × String) := #[]
  errors : HashSet String := {}

def TraverseState.addJsFile (st : TraverseState) (name content : String) :=
  if st.jsFiles.all (·.1 != name) then
    {st with jsFiles := st.jsFiles.push (name, content)}
  else st

def TraverseState.addCssFile (st : TraverseState) (name content : String) :=
  if st.cssFiles.all (·.1 != name) then
    {st with cssFiles := st.cssFiles.push (name, content)}
  else st

structure PartMetadata where
  tag : String

def Page : Genre where
  PartMetadata := PartMetadata
  Block := BlockExt
  Inline := InlineExt
  TraverseContext := TraverseContext
  TraverseState := TraverseState

partial def TraverseState.freshId (state : TraverseState) (path : List String) (hint : Lean.Name) : String := Id.run do
  let mut idStr := mangle (toString hint)
  match state.usedIds.find? path with
  | none => return idStr
  | some used =>
    while used.contains idStr do
      idStr := next idStr
    return idStr
where
  next (idStr : String) : String :=
    match idStr.takeRightWhile (·.isDigit) with
    | "" => idStr ++ "1"
    | more =>
      if let some n := more.toNat? then
        idStr.dropRight (more.length) ++ toString (n + 1)
      else
        idStr.dropRight (more.length) ++ "1"
  mangle (idStr : String) : String := Id.run do
    let mut state := false -- found valid leading char?
    let mut out := ""
    for c in idStr.toList do
      if state == false then
        if c.isAlpha then
          state := true
          out := out.push c
      else
        if c.isAlphanum || c ∈ [':', '-', ':', '.'] then
          out := out.push c
        else
          out := out ++ s!"--{c.toNat}--"
    pure out


instance : BEq TraverseState where
  beq
    | ⟨u1, t1, s1, s1', js1, css1, err1⟩, ⟨u2, t2, s2, s2', js2, css2, err2⟩ =>
      u1.toList.map (fun p => {p with snd := p.snd.toList}) == u2.toList.map (fun p => {p with snd := p.snd.toList}) &&
      t1.toList == t2.toList &&
      s1.toList == s2.toList &&
      s1'.toList == s2'.toList &&
      js1.size == js2.size &&
      js1.all (js2.contains ·) &&
      css1.size == css2.size &&
      css1.all (css2.contains ·) &&
      err1.toList == err2.toList

abbrev TraverseM := ReaderT TraverseContext (StateT TraverseState IO)

instance : MonadConfig TraverseM where
  currentConfig := do pure (← read).config

namespace Traverse

open Doc

def renderMathJs : String :=
"document.addEventListener(\"DOMContentLoaded\", () => {
    for (const m of document.querySelectorAll(\".math.inline\")) {
        katex.render(m.textContent, m, {throwOnError: false, displayMode: false});
    }
    for (const m of document.querySelectorAll(\".math.display\")) {
        katex.render(m.textContent, m, {throwOnError: false, displayMode: true});
    }
});"

def highlightingJs_withFlean : String :=
"
window.onload = () => {

    // Don't show hovers inside of closed tactic states
    function blockedByTactic(elem) {
      let parent = elem.parentNode;
      while (parent && \"classList\" in parent) {
        if (parent.classList.contains(\"tactic\")) {
          const toggle = parent.querySelector(\"input.tactic-toggle\");
          if (toggle) {
            return !toggle.checked;
          }
        }
        parent = parent.parentNode;
      }
      return false;
    }

    function blockedByTippy(elem) {
      // Don't show a new hover until the old ones are all closed.
      // Scoped to the nearest \"top-level block\" to avoid being O(n) in the size of the document.
      var block = elem;
      const topLevel = new Set([\"section\", \"body\", \"html\", \"nav\", \"header\"]);
      while (block.parentNode && !topLevel.has(block.parentNode.nodeName.toLowerCase())) {
        block = block.parentNode;
      }
      for (const child of block.querySelectorAll(\".token, .has-info\")) {
        if (child._tippy && child._tippy.state.isVisible) { return true };
      }
      return false;
    }

    for (const c of document.querySelectorAll(\".hl.lean .token\")) {
        if (c.dataset.binding != \"\") {
            c.addEventListener(\"mouseover\", (event) => {
                if (blockedByTactic(c)) {return;}
                const context = c.closest(\".hl.lean\").dataset.leanContext;
                for (const example of document.querySelectorAll(\".hl.lean\")) {
                    if (example.dataset.leanContext == context) {
                        for (const tok of example.querySelectorAll(\".token\")) {
                            if (c.dataset.binding == tok.dataset.binding) {
                                tok.classList.add(\"binding-hl\");
                            }
                        }
                    }
                }
            });
        }
        c.addEventListener(\"mouseout\", (event) => {
            for (const tok of document.querySelectorAll(\".hl.lean .token\")) {
                tok.classList.remove(\"binding-hl\");
            }
        });
    }
    /* Render docstrings */
    if ('undefined' !== typeof marked) {
        for (const d of document.querySelectorAll(\"code.docstring, pre.docstring\")) {
            const str = d.innerText;
            const html = marked.parse(str);
            const rendered = document.createElement(\"div\");
            rendered.classList.add(\"docstring\");
            rendered.innerHTML = html;
            d.parentNode.replaceChild(rendered, d);
        }
    }
    // Add hovers
    let siteRoot = typeof __versoSiteRoot !== 'undefined' ? __versoSiteRoot : \"/\";
    fetch(siteRoot + \"flean/verso-docs.json\").then((resp) => resp.json()).then((versoDocData) => {

      const defaultTippyProps = {
        /* DEBUG -- remove the space: * /
        onHide(any) { return false; },
        trigger: \"click\",
        // */
        theme: \"lean\",
        maxWidth: \"none\",
        appendTo: () => document.body,
        interactive: true,
        delay: [100, null],
        ignoreAttributes: true,
        onShow(inst) {
          if (inst.reference.querySelector(\".hover-info\") || \"versoHover\" in inst.reference.dataset) {
            if (blockedByTactic(inst.reference)) { return false };
            if (blockedByTippy(inst.reference)) { return false; }
          } else { // Nothing to show here!
            return false;
          }
        },
        content (tgt) {
          const content = document.createElement(\"span\");
          content.className = \"hl lean\";
          content.style.display = \"block\";
          content.style.maxHeight = \"300px\";
          content.style.overflowY = \"auto\";
          content.style.overflowX = \"hidden\";
          const hoverId = tgt.dataset.versoHover;
          const hoverInfo = tgt.querySelector(\".hover-info\");
          if (hoverId) { // Docstrings from the table
            // TODO stop doing an implicit conversion from string to number here
            let data = versoDocData[hoverId];
            if (data) {
              const info = document.createElement(\"span\");
              info.className = \"hover-info\";
              info.style.display = \"block\";
              info.innerHTML = data;
              content.appendChild(info);
              /* Render docstrings - TODO server-side */
              if ('undefined' !== typeof marked) {
                  for (const d of content.querySelectorAll(\"code.docstring, pre.docstring\")) {
                      const str = d.innerText;
                      const html = marked.parse(str);
                      const rendered = document.createElement(\"div\");
                      rendered.classList.add(\"docstring\");
                      rendered.innerHTML = html;
                      d.parentNode.replaceChild(rendered, d);
                  }
              }
            } else {
              content.innerHTML = \"Failed to load doc ID: \" + hoverId;
            }
          } else if (hoverInfo) { // The inline info, still used for compiler messages
            content.appendChild(hoverInfo.cloneNode(true));
          }
          return content;
        }
      };

      const addTippy = (selector, props) => {
        tippy(selector, Object.assign({}, defaultTippyProps, props));
      };
      addTippy('.hl.lean .const.token, .hl.lean .keyword.token, .hl.lean .literal.token, .hl.lean .option.token, .hl.lean .var.token, .hl.lean .typed.token', {theme: 'lean'});
      addTippy('.hl.lean .has-info.warning', {theme: 'warning message'});
      addTippy('.hl.lean .has-info.info', {theme: 'info message'});
      addTippy('.hl.lean .has-info.error', {theme: 'error message'});

      tippy('.hl.lean .tactic', {
        allowHtml: true,
        /* DEBUG -- remove the space: * /
        onHide(any) { return false; },
        trigger: \"click\",
        // */
        maxWidth: \"none\",
        onShow(inst) {
          const toggle = inst.reference.querySelector(\"input.tactic-toggle\");
          if (toggle && toggle.checked) {
            return false;
          }
          if (blockedByTippy(inst.reference)) { return false; }
        },
        theme: \"tactic\",
        placement: 'bottom-start',
        content (tgt) {
          const content = document.createElement(\"span\");
          const state = tgt.querySelector(\".tactic-state\").cloneNode(true);
          state.style.display = \"block\";
          content.appendChild(state);
          content.style.display = \"block\";
          content.className = \"hl lean popup\";
          return content;
        }
      });
  });
}
"

def genreBlock : BlockExt → Array (Block Page) → TraverseM (Option (Block Page))
    | .highlightedCode .., _contents => do
      modify fun st => {st with
        stylesheets := st.stylesheets.insert highlightingStyle,
        scripts := st.scripts.insert highlightingJs_withFlean
      } |>.addJsFile "popper.js" popper |>.addJsFile "tippy.js" tippy |>.addCssFile "tippy-border.css" tippy.border.css
      pure none
    | _, _ => pure none

def genreInline : InlineExt → Array (Inline Page) → TraverseM (Option (Inline Page))
    | .highlightedCode .., _contents | .customHighlight .., _contents => do
      modify fun st => {st with
        stylesheets := st.stylesheets.insert highlightingStyle,
        scripts := st.scripts.insert highlightingJs_withFlean
      } |>.addJsFile "popper.js" popper |>.addJsFile "tippy.js" tippy |>.addCssFile "tippy-border.css" tippy.border.css
      pure none
    | .label x, _contents => do
      -- Add as target if not already present
      if let none := (← get).targets.find? x then
        let path := (← read).path
        let htmlId := (← get).freshId path x
        modify fun st => {st with targets := st.targets.insert x ⟨path, htmlId⟩}
      pure none
    | .ref _x, _contents =>
      -- TODO backreference
      pure none
    | .htmlSpan .., _ | .blob .., _ => pure none

instance : Traverse Page TraverseM  where
  part _ := pure none
  block _ := pure ()
  inline _ := pure ()
  genrePart _ _ := pure none
  genreBlock := genreBlock
  genreInline := genreInline

instance : TraversePart Page := {}

end Traverse


open HtmlT

defmethod LexedText.toHtml (text : LexedText) : Html :=
  text.content.map fun
    | (none, txt) => (txt : Html)
    | (some cls, txt) => {{ <span class={{cls}}>{{txt}}</span>}}

def blockHtml (_goI : Inline Page → HtmlT Page IO Html) (goB : Block Page → HtmlT Page IO Html) : BlockExt → Array (Block Page) → HtmlT Page IO Html
  | .lexedText content, _contents => do
    pure {{ <pre class=s!"lexed {content.name}"> {{ content.toHtml }} </pre> }}
  | .highlightedCode contextName hls, _contents => hls.blockHtml (toString contextName)
  | .htmlDetails classes, contents => do
    pure {{ <details class={{classes}}> {{← contents.mapM goB}}</details>}}
  | .htmlWrapper name attrs, contents => do
    Html.tag name attrs <$> contents.mapM goB
  | .htmlDiv classes, contents => do
    pure {{ <div class={{classes}}> {{← contents.mapM goB}} </div> }}
  | .blob html, _ => pure html

class MonadPath (m : Type → Type u) where
  currentPath : m (List String)

instance [Monad m] : MonadPath (HtmlT Page m) where
  currentPath := do
    return (← context).path

instance [Monad m] : MonadConfig (HtmlT Page m) where
  currentConfig := do
    return (← context).config

def relative [Monad m] [MonadConfig m] [mp : MonadPath m] (target : List String) : m (List String) := do
  return relativize (← mp.currentPath) target
where
  relativize (me target : List String) : List String :=
    match me, target with
    | [], any => any
    | any, [] => any.map (fun _ => "..")
    | x :: xs, y :: ys =>
      if x == y then
        relativize xs ys
      else
        (x :: xs).map (fun _ => "..") ++ (y :: ys)

def inlineHtml [MonadConfig (HtmlT Page IO)] [MonadPath (HtmlT Page IO)]
    (go : Inline Page → HtmlT Page IO Html) : InlineExt → Array (Inline Page) → HtmlT Page IO Html
  | .highlightedCode contextName hls, _contents => hls.inlineHtml (some <| toString contextName)
  | .customHighlight hls, _contents => hls.inlineHtml none
  | .label x, contents => do
    let contentHtml ← contents.mapM go
    let st ← state
    let some tgt := st.targets.find? x
      | panic! "No label for {x}"
    pure {{ <span id={{tgt.htmlId}}> {{ contentHtml }} </span>}}
  | .ref x, contents => do
    let st ← state
    match st.targets.find? x with
    | none =>
      HtmlT.logError "Can't find target {x}"
      pure {{<strong class="internal-error">s!"Can't find target {x}"</strong>}}
    | some tgt =>
      let addr := s!"{String.join ((← relative tgt.path).intersperse "/")}#{tgt.htmlId}"
      go <| .link contents addr
  | .htmlSpan classes, contents => do
    pure {{ <span class={{classes}}> {{← contents.mapM go}} </span> }}
  | .blob html, _ => pure html

instance : GenreHtml Page IO where
  part f m := (
    (fun go _metadata part => go part : (Part Page → (mkHeader : Nat → Html → Html := mkPartHeader) → HtmlT Page IO Html) → Page.PartMetadata → Part Page → HtmlT Page IO Html)
  ) (fun p mkHd => f p mkHd) m
  block := blockHtml
  inline := inlineHtml

open Verso.Output Html
open Lean (RBMap)

open Lean Elab
open Verso ArgParse Doc Elab

open SubVerso.Examples (loadExamples Example)


def classArgs : ArgParse DocElabM String := .named `«class» .string false

@[role_expander htmlSpan]
def htmlSpan : RoleExpander
  | args, stxs => do
    let classes ← classArgs.run args
    let contents ← stxs.mapM elabInline
    let val ← ``(Inline.other (InlineExt.htmlSpan $(quote classes)) #[$contents,*])
    pure #[val]

@[directive_expander htmlDiv]
def htmlDiv : DirectiveExpander
  | args, stxs => do
    let classes ← classArgs.run args
    let contents ← stxs.mapM elabBlock
    let val ← ``(Block.other (BlockExt.htmlDiv $(quote classes)) #[ $contents,* ])
    pure #[val]

private partial def attrs : ArgParse DocElabM (Array (String × String)) := List.toArray <$> remaining attr
where
  remaining {m} {α} (p : ArgParse m α) : ArgParse m (List α) :=
    (.done *> pure []) <|> ((· :: ·) <$> p <*> remaining p)
  attr : ArgParse DocElabM (String × String) :=
    (fun (k, v) => (k.getId.toString (escape := false), v)) <$> .anyNamed "attribute" .string

@[directive_expander html]
def html : DirectiveExpander
  | args, stxs => do
    let (name, attrs) ← ArgParse.run ((·, ·) <$> .positional `name .name <*> attrs) args
    let tag := name.toString (escape := false)
    let contents ← stxs.mapM elabBlock
    let val ← ``(Block.other (BlockExt.htmlWrapper $(quote tag) $(quote attrs)) #[ $contents,* ])
    pure #[val]

@[directive_expander blob]
def blob : DirectiveExpander
  | #[.anon (.name blobName)], stxs => do
    if h : stxs.size > 0 then logErrorAt stxs[0] "Expected no contents"
    let actualName ← realizeGlobalConstNoOverloadWithInfo blobName
    let val ← ``(Block.other (BlockExt.blob ($(mkIdentFrom blobName actualName) : Html)) #[])
    pure #[val]
  | _, _ => throwUnsupportedSyntax

@[role_expander blob]
def inlineBlob : RoleExpander
  | #[.anon (.name blobName)], stxs => do
    if h : stxs.size > 0 then logErrorAt stxs[0] "Expected no contents"
    let actualName ← realizeGlobalConstNoOverloadWithInfo blobName
    let val ← ``(Inline.other (InlineExt.blob ($(mkIdentFrom blobName actualName) : Html)) #[])
    pure #[val]
  | _, _ => throwUnsupportedSyntax

@[role_expander label]
def label : RoleExpander
  | #[.anon (.name l)], stxs => do
    let args ← stxs.mapM elabInline
    let val ← ``(Inline.other (InlineExt.label $(quote l.getId)) #[ $[ $args ],* ])
    pure #[val]
  | _, _ => throwUnsupportedSyntax

@[role_expander ref]
def ref : RoleExpander
  | #[.anon (.name l)], stxs => do
    let args ← stxs.mapM elabInline
    let val ← ``(Inline.other (InlineExt.ref $(quote l.getId)) #[ $[ $args ],* ])
    pure #[val]
  | _, _ => throwUnsupportedSyntax


@[role_expander page_link]
def page_link : RoleExpander
  | #[.anon (.name page)], stxs => do
    let args ← stxs.mapM elabInline
    let pageName := mkIdentFrom page <| docName page.getId
    let val ← ``(Inline.other (InlineExt.pageref $(quote pageName.getId)) #[ $[ $args ],* ])
    pure #[val]
  | _, _ => throwUnsupportedSyntax


-- The assumption here is that suffixes are _mostly_ unique, so the arrays will likely be very
-- small.
structure NameSuffixMap (α : Type) : Type where
  contents : NameMap (Array (Name × α)) := {}
deriving Inhabited

def NameSuffixMap.empty : NameSuffixMap α := {}

def NameSuffixMap.insert (map : NameSuffixMap α) (key : Name) (val : α) : NameSuffixMap α := Id.run do
  let some last := key.components.getLast?
    | map
  let mut arr := map.contents.find? last |>.getD #[]
  for h : i in [0:arr.size] do
    have : i < arr.size := by get_elem_tactic
    if arr[i].fst == key then
      return {map with contents := map.contents.insert last (arr.set i (key, val))}
  return {map with contents := map.contents.insert last (arr.push (key, val))}

def NameSuffixMap.toArray (map : NameSuffixMap α) : Array (Name × α) := Id.run do
  let mut arr := #[]
  for (_, arr') in map.contents.toList do
    arr := arr ++ arr'
  arr.qsort (fun x y => x.fst.toString < y.fst.toString)

def NameSuffixMap.toList (map : NameSuffixMap α) : List (Name × α) := map.toArray.toList

def NameSuffixMap.get (map : NameSuffixMap α) (key : Name) : Array (Name × α) := Id.run do
  let ks := key.componentsRev
  let some k' := ks.head?
    | #[]
  let some candidates := map.contents.find? k'
    | #[]
  let mut result := none
  for (n, c) in candidates do
    match matchLength ks n.componentsRev, result with
    | none, _ => continue
    | some l, none => result := some (l, #[(n, c)])
    | some l, some (l', found) =>
      if l > l' then result := some (l, #[(n, c)])
      else if l == l' then result := some (l', found.push (n, c))
      else continue
  let res := result.map Prod.snd |>.getD #[]
  res.qsort (fun x y => x.fst.toString < y.fst.toString)
where
  matchLength : List Name → List Name → Option Nat
    | [], _ => some 0
    | _ :: _, [] => none
    | x::xs, y::ys =>
      if x == y then
        matchLength xs ys |>.map (· + 1)
      else none

/-- info: #[(`a.b.c, 1), (`a.c, 4), (`b.c, 6), (`c, 3)] -/
#guard_msgs in
#eval NameSuffixMap.empty |>.insert `a.b.c 1 |>.insert `b.c 2 |>.insert `c 3 |>.insert `a.c 4 |>.insert `a.b 5 |>.insert `b.c 6 |>.get `c

inductive LeanExampleData where
  | inline (commandState : Command.State) (parserState : Parser.ModuleParserState)
  | subproject (loaded : NameSuffixMap Example)
deriving Inhabited

structure ExampleContext where
  contexts : NameMap LeanExampleData := {}
deriving Inhabited

initialize exampleContextExt : EnvExtension ExampleContext ← registerEnvExtension (pure {})

structure ExampleMessages where
  messages : NameSuffixMap (MessageLog ⊕ List (MessageSeverity × String)) := {}
deriving Inhabited

initialize messageContextExt : EnvExtension ExampleMessages ← registerEnvExtension (pure {})

-- FIXME this is a horrid kludge - find a way to systematically rewrite srclocs?
def parserInputString [Monad m] [MonadFileMap m] (str : TSyntax `str) : m String := do
  let preString := (← getFileMap).source.extract 0 (str.raw.getPos?.getD 0)
  let mut code := ""
  let mut iter := preString.iter
  while !iter.atEnd do
    if iter.curr == '\n' then code := code.push '\n'
    else
      for _ in [0:iter.curr.utf8Size] do
        code := code.push ' '
    iter := iter.next
  code := code ++ str.getString
  return code

initialize registerTraceClass `Elab.Verso.block.lean


open System in
@[block_role_expander leanExampleProject]
def leanExampleProject : BlockRoleExpander
  | args, #[] => withTraceNode `Elab.Verso.block.lean (fun _ => pure m!"Loading example project") <| do
    let (name, projectDir) ← ArgParse.run ((·, ·) <$> .positional `name .name <*> .positional `projectDir .string) args
    if exampleContextExt.getState (← getEnv) |>.contexts |>.contains name then
      throwError "Example context '{name}' already defined in this module"
    let path : FilePath := ⟨projectDir⟩
    if path.isAbsolute then
      throwError "Expected a relative path, got {path}"
    let loadedExamples ← loadExamples path
    let mut savedExamples := {}
    for (mod, modExamples) in loadedExamples.toList do
      for (exName, ex) in modExamples.toList do
        savedExamples := savedExamples.insert (mod ++ exName) ex
    modifyEnv fun env => exampleContextExt.modifyState env fun s => {s with
      contexts := s.contexts.insert name (.subproject savedExamples)
    }
    for (name, ex) in savedExamples.toArray do
      modifyEnv fun env => messageContextExt.modifyState env fun s => {s with messages := s.messages.insert name (.inr ex.messages) }
    Verso.Hover.addCustomHover (← getRef) <| "Contains:\n" ++ String.join (savedExamples.toList.map (s!" * `{toString ·.fst}`\n"))
    pure #[]
  | _, more =>
    if h : more.size > 0 then
      throwErrorAt more[0] "Unexpected contents"
    else
      throwError "Unexpected contents"
where
  getModExamples (mod : Name) (json : Json) : DocElabM (NameMap Example) := do
    let .ok exs := json.getObj?
      | throwError "Not an object: '{json}'"
    let mut found := {}
    for ⟨name, exJson⟩ in exs.toArray do
      match FromJson.fromJson? exJson with
      | .error err =>
        throwError "Error deserializing example '{name}' in '{mod}': {err}\nfrom:\n{json}"
      | .ok ex => found := found.insert (mod ++ name.toName) ex
    pure found

private def getSubproject (project : Ident) : TermElabM (NameSuffixMap Example) := do
  let some ctxt := exampleContextExt.getState (← getEnv) |>.contexts |>.find? project.getId
    | throwErrorAt project "Subproject '{project}' not loaded"
  let .subproject projectExamples := ctxt
    | throwErrorAt project "'{project}' is not loaded as a subproject"
  Verso.Hover.addCustomHover project <| "Contains:\n" ++ String.join (projectExamples.toList.map (s!" * `{toString ·.fst}`\n"))
  pure projectExamples

def NameSuffixMap.getOrSuggest [Monad m] [MonadInfoTree m] [MonadError m]
    (map : NameSuffixMap α) (key : Ident) : m (Name × α) := do
  match map.get key.getId with
  | #[(n', v)] =>
    if n' ≠ key.getId then
      Suggestion.saveSuggestion key n'.toString n'.toString
    pure (n', v)
  | #[] =>
    for (n, _) in map.toArray do
      if FuzzyMatching.fuzzyMatch key.getId.toString n.toString then
        Suggestion.saveSuggestion key n.toString n.toString
    throwErrorAt key "'{key}' not found - options are {map.toList.map (·.fst)}"
  | more =>
    for (n, _) in more do
      Suggestion.saveSuggestion key n.toString n.toString
    throwErrorAt key "'{key}' is ambiguous - options are {more.toList.map (·.fst)}"

@[block_role_expander leanCommand]
def leanCommand : BlockRoleExpander
  | args, #[] => withTraceNode `Elab.Verso.block.lean (fun _ => pure m!"leanCommand") <| do
    let (project, exampleName) ← ArgParse.run ((·, ·) <$> .positional `project .ident <*> .positional `exampleName .ident) args
    let projectExamples ← getSubproject project
    let (_, {highlighted := hls, original := str, ..}) ← projectExamples.getOrSuggest exampleName
    Verso.Hover.addCustomHover exampleName s!"```lean\n{str}\n```"
    pure #[← ``(Block.other (BlockExt.highlightedCode $(quote project.getId) (SubVerso.Highlighting.Highlighted.seq $(quote hls))) #[Block.code $(quote str)])]
  | _, more =>
    if h : more.size > 0 then
      throwErrorAt more[0] "Unexpected contents"
    else
      throwError "Unexpected contents"

@[role_expander leanKw]
def leanKw : RoleExpander
  | args, #[arg] => do
    ArgParse.run .done args
    let `(inline|code( $kw:str )) := arg
      | throwErrorAt arg "Expected code literal with the keyword"
    let hl : SubVerso.Highlighting.Highlighted := .token ⟨.keyword none none none, kw.getString⟩
    pure #[← ``(Inline.other (InlineExt.customHighlight $(quote hl)) #[Inline.code $(quote kw.getString)])]
  | _, more =>
    if h : more.size > 0 then
      throwErrorAt more[0] "Unexpected contents"
    else
      throwError "Unexpected arguments"

@[role_expander leanTerm]
def leanTerm : RoleExpander
  | args, #[arg] => withTraceNode `Elab.Verso.block.lean (fun _ => pure m!"leanTerm") <| do
    let project ← ArgParse.run (.positional `project .ident) args
    let `(inline|code( $name:str )) := arg
      | throwErrorAt arg "Expected code literal with the example name"
    let exampleName := name.getString.toName
    let projectExamples ← getSubproject project
    let (_, {highlighted := hls, original := str, ..}) ← projectExamples.getOrSuggest <| mkIdentFrom name exampleName
    Verso.Hover.addCustomHover arg s!"```lean\n{str}\n```"
    pure #[← ``(Inline.other (InlineExt.highlightedCode $(quote project.getId) (SubVerso.Highlighting.Highlighted.seq $(quote hls))) #[Inline.code $(quote str)])]
  | _, more =>
    if h : more.size > 0 then
      throwErrorAt more[0] "Unexpected contents"
    else
      throwError "Unexpected arguments"


structure LeanBlockConfig where
  exampleContext : Ident
  «show» : Option Bool := none
  keep : Option Bool := none
  name : Option Name := none
  error : Option Bool := none

def LeanBlockConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m LeanBlockConfig :=
  LeanBlockConfig.mk <$> .positional `exampleContext .ident <*> .named `show .bool true <*> .named `keep .bool true <*> .named `name .name true <*> .named `error .bool true

@[code_block_expander leanInit]
def leanInit : CodeBlockExpander
  | args , str => withTraceNode `Elab.Verso.block.lean (fun _ => pure m!"leanInit") <| do
    let config ← LeanBlockConfig.parse.run args
    let context := Parser.mkInputContext (← parserInputString str) (← getFileName)
    let (header, state, msgs) ← Parser.parseHeader context
    for imp in header[1].getArgs do
      logErrorAt imp "Imports not yet supported here"
    let opts := Options.empty -- .setBool `trace.Elab.info true
    if header[0].isNone then -- if the "prelude" option was not set, use the current env
      let commandState := configureCommandState (←getEnv) {}
      modifyEnv <| fun env => exampleContextExt.modifyState env fun s => {s with contexts := s.contexts.insert config.exampleContext.getId (.inline commandState  state)}
    else
      if header[1].getArgs.isEmpty then
        let (env, msgs) ← processHeader header opts msgs context 0
        if msgs.hasErrors then
          for msg in msgs.toList do
            logMessage msg
          liftM (m := IO) (throw <| IO.userError "Errors during import; aborting")
        let commandState := configureCommandState env {}
        modifyEnv <| fun env => exampleContextExt.modifyState env fun s => {s with contexts := s.contexts.insert config.exampleContext.getId (.inline commandState state)}
    if config.show.getD false then
      pure #[← ``(Block.code $(quote str.getString))] -- TODO highlighting hack
    else pure #[]
where
  configureCommandState (env : Environment) (msg : MessageLog) : Command.State :=
    { Command.mkState env msg with infoState := { enabled := true } }

open SubVerso.Highlighting Highlighted in
@[code_block_expander lean]
def lean : CodeBlockExpander
  | args, str => withTraceNode `Elab.Verso.block.lean (fun _ => pure m!"lean block") <| do
    let config ← LeanBlockConfig.parse.run args
    let x := config.exampleContext
    let (commandState, state) ← match exampleContextExt.getState (← getEnv) |>.contexts.find? x.getId with
      | some (.inline commandState state) => pure (commandState, state)
      | some (.subproject ..) => throwErrorAt x "Expected an example context for inline Lean, but found a subproject"
      | none => throwErrorAt x "Can't find example context"
    let context := Parser.mkInputContext (← parserInputString str) (← getFileName)
    -- Process with empty messages to avoid duplicate output
    let s ←
      withTraceNode `Elab.Verso.block.lean (fun _ => pure m!"Elaborating commands") <|
      IO.processCommands context state { commandState with messages.unreported := {} }
    for t in s.commandState.infoState.trees do
      pushInfoTree t

    match config.error with
    | none =>
      for msg in s.commandState.messages.toArray do
        logMessage msg
    | some true =>
      if s.commandState.messages.hasErrors then
        for msg in s.commandState.messages.errorsToWarnings.toArray do
          logMessage msg
      else
        throwErrorAt str "Error expected in code block, but none occurred"
    | some false =>
      for msg in s.commandState.messages.toArray do
        logMessage msg
      if s.commandState.messages.hasErrors then
        throwErrorAt str "No error expected in code block, one occurred"

    if config.keep.getD true && !(config.error.getD false) then
      modifyEnv fun env => exampleContextExt.modifyState env fun st => {st with
        contexts := st.contexts.insert x.getId (.inline {s.commandState with messages := {} } s.parserState)
      }
    if let some infoName := config.name then
      modifyEnv fun env => messageContextExt.modifyState env fun st => {st with
        messages := st.messages.insert infoName (.inl s.commandState.messages)
      }
    withTraceNode `Elab.Verso.block.lean (fun _ => pure m!"Highlighting syntax") do
      let mut hls := Highlighted.empty
      let infoSt ← getInfoState
      let env ← getEnv
      try
        setInfoState s.commandState.infoState
        setEnv s.commandState.env
        let msgs := s.commandState.messages.toArray
        for cmd in s.commands do
          hls := hls ++
            (← withTraceNode `Elab.Verso.block.lean (fun _ => pure m!"Highlighting {cmd}") <|
              highlight cmd msgs s.commandState.infoState.trees)
      finally
        setInfoState infoSt
        setEnv env
      if config.show.getD true then
        pure #[← ``(Block.other (BlockExt.highlightedCode $(quote x.getId) $(quote hls)) #[Block.code $(quote str.getString)])]
      else
        pure #[]

open Lean.Elab.Tactic.GuardMsgs
export WhitespaceMode (exact lax normalized)

structure LeanOutputConfig where
  name : Ident
  severity : Option MessageSeverity
  summarize : Bool
  whitespace : WhitespaceMode

def LeanOutputConfig.parser [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m LeanOutputConfig :=
  LeanOutputConfig.mk <$>
    .positional `name output <*>
    .named `severity sev true <*>
    ((·.getD false) <$> .named `summarize .bool true) <*>
    ((·.getD .exact) <$> .named `whitespace ws true)
where
  output : ValDesc m Ident := {
    description := "output name",
    get := fun
      | .name x => pure x
      | other => throwError "Expected output name, got {repr other}"
  }
  opt {α} (p : ArgParse m α) : ArgParse m (Option α) := (some <$> p) <|> pure none
  optDef {α} (fallback : α) (p : ArgParse m α) : ArgParse m α := p <|> pure fallback
  sev : ValDesc m MessageSeverity := {
    description := open MessageSeverity in m!"The expected severity: '{``error}', '{``warning}', or '{``information}'",
    get := open MessageSeverity in fun
      | .name b => do
        let b' ← realizeGlobalConstNoOverloadWithInfo b
        if b' == ``MessageSeverity.error then pure MessageSeverity.error
        else if b' == ``MessageSeverity.warning then pure MessageSeverity.warning
        else if b' == ``MessageSeverity.information then pure MessageSeverity.information
        else throwErrorAt b "Expected '{``error}', '{``warning}', or '{``information}'"
      | other => throwError "Expected severity, got {repr other}"
  }
  ws : ValDesc m WhitespaceMode := {
    description := open WhitespaceMode in m!"The expected whitespace mode: '{``exact}', '{``normalized}', or '{``lax}'",
    get := open WhitespaceMode in fun
      | .name b => do
        let b' ← realizeGlobalConstNoOverloadWithInfo b
        if b' == ``WhitespaceMode.exact then pure WhitespaceMode.exact
        else if b' == ``WhitespaceMode.normalized then pure WhitespaceMode.normalized
        else if b' == ``WhitespaceMode.lax then pure WhitespaceMode.lax
        else throwErrorAt b "Expected '{``exact}', '{``normalized}', or '{``lax}'"
      | other => throwError "Expected whitespace mode, got {repr other}"
  }

@[code_block_expander leanOutput]
def leanOutput : Doc.Elab.CodeBlockExpander
  | args, str => withTraceNode `Elab.Verso.block.lean (fun _ => pure m!"leanOutput") <| do
    let config ← LeanOutputConfig.parser.run args

    let (_, savedInfo) ← messageContextExt.getState (← getEnv) |>.messages |>.getOrSuggest config.name
    let messages ← match savedInfo with
      | .inl log =>
        let messages ← liftM <| log.toArray.mapM contents
        for m in log.toArray do
          if mostlyEqual config.whitespace str.getString (← contents m) then
            if let some s := config.severity then
              if s != m.severity then
                throwErrorAt str s!"Expected severity {sevStr s}, but got {sevStr m.severity}"
            let content ← if config.summarize then
                let lines := str.getString.splitOn "\n"
                let pre := lines.take 3
                let post := String.join (lines.drop 3 |>.intersperse "\n")
                let preHtml : Html := pre.map (fun (l : String) => {{<code>{{l}}</code>}})
                ``(Block.other (BlockExt.htmlDetails $(quote (sevStr m.severity)) $(quote preHtml)) #[Block.code $(quote post)])
              else
                ``(Block.other (BlockExt.htmlDiv $(quote (sevStr m.severity))) #[Block.code $(quote str.getString)])
            return #[content]
        pure messages
      | .inr msgs =>
        let messages := msgs.toArray.map Prod.snd
        for (sev, txt) in msgs do
          if mostlyEqual config.whitespace str.getString txt then
            if let some s := config.severity then
              if s != sev then
                throwErrorAt str s!"Expected severity {sevStr s}, but got {sevStr sev}"
            let content ← if config.summarize then
                let lines := str.getString.splitOn "\n"
                let pre := lines.take 3
                let post := String.join (lines.drop 3 |>.intersperse "\n")
                let preHtml : Html := pre.map (fun (l : String) => {{<code>{{l}}</code>}})
                ``(Block.other (BlockExt.htmlDetails $(quote (sevStr sev)) $(quote preHtml)) #[Block.code $(quote post)])
              else
                ``(Block.other (BlockExt.htmlDiv $(quote (sevStr sev))) #[Block.code $(quote str.getString)])
            return #[content]
        pure messages

    for m in messages do
      Verso.Doc.Suggestion.saveSuggestion str (m.take 30 ++ "…") m
    throwErrorAt str "Didn't match - expected one of: {indentD (toMessageData messages)}\nbut got:{indentD (toMessageData str.getString)}"
where
  withNewline (str : String) := if str == "" || str.back != '\n' then str ++ "\n" else str

  sevStr : MessageSeverity → String
    | .error => "error"
    | .information => "information"
    | .warning => "warning"

  contents (message : Message) : IO String := do
    let head := if message.caption != "" then message.caption ++ ":\n" else ""
    pure <| withNewline <| head ++ (← message.data.toString)

  mostlyEqual (ws : WhitespaceMode) (s1 s2 : String) : Bool :=
    ws.apply s1.trim == ws.apply s2.trim

open Lean Elab Command in
elab "#defineLexerBlock" blockName:ident " ← " lexerName:ident : command => do
  let lexer ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo lexerName
  elabCommand <| ← `(@[code_block_expander $blockName]
    def $blockName : Doc.Elab.CodeBlockExpander
      | #[], str => do
        let out ← LexedText.highlight $(mkIdentFrom lexerName lexer) str.getString
        return #[← ``(Block.other (Blog.BlockExt.lexedText $$(quote out)) #[])]
      | _, str => throwErrorAt str "Expected no arguments")


private def filterString (p : Char → Bool) (str : String) : String := Id.run <| do
  let mut out := ""
  for c in str.toList do
    if p c then out := out.push c
  pure out

def ensureDir (dir : System.FilePath) : IO Unit := do
  if !(← dir.pathExists) then
    IO.FS.createDirAll dir
  if !(← dir.isDir) then
    throw (↑ s!"Not a directory: {dir}")


structure HeaderInfo where
  name : String
  builtInStyles : Std.HashSet String
  builtInScripts : Std.HashSet String
  jsFiles : Array String
  cssFiles : Array String

def getHeaderInfo (t : TraverseState) : HeaderInfo where
  name := "flean"
  builtInStyles := t.stylesheets
  builtInScripts := t.scripts.insert Traverse.renderMathJs
  jsFiles := t.jsFiles.map (·.1)
  cssFiles := t.cssFiles.map (·.1)

def getHeader (h : HeaderInfo): Html := Id.run do
  let mut out := .empty
  for style in h.builtInStyles do
    out := out ++ {{<style>"\n"{{.text false style}}"\n"</style>"\n"}}
  for script in h.builtInScripts do
    out := out ++ {{<script>"\n"{{.text false script}}"\n"</script>"\n"}}
  for js in h.jsFiles do
    out := out ++ {{<script src=s!"/{h.name}/verso-js/{js}"></script>}}
  for css in h.cssFiles do
    out := out ++ {{<link rel="stylesheet" href=s!"/{h.name}/verso-css/{css}"/>}}
  return out ++ {{
    <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.css" integrity="sha384-n8MVd4RsNIU0tAv4ct0nTaAbDJwPJzDEaqSD1odI+WdtXRGWt2kTvGFasHpSy3SV" crossorigin="anonymous"/>
    <script defer="defer" src="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.js" integrity="sha384-XjKyOOlGwcjNTAIQHIpgOno0Hl1YQqzUOEleOLALmuqehneUG+vnGctmUb0ZY0l8" crossorigin="anonymous"></script>
    <script src="https://cdn.jsdelivr.net/npm/marked@11.1.1/marked.min.js" integrity="sha384-zbcZAIxlvJtNE3Dp5nxLXdXtXyxwOdnILY1TDPVmKFhl4r4nSUG1r8bcFXGVa4Te" crossorigin="anonymous"></script>
  }}


def renderPage (doc : Part Page) : IO UInt32 := do
  let mut doc := doc
  -- Do the traversal pass until either too many iterations have been reached (indicating a bug) or
  -- a fixed point is reached
  let mut state : TraverseState := {}
  let hasError ← IO.mkRef false
  let logError msg := do hasError.set true; IO.eprintln msg
  let cfg : Config := {logError := logError}
  -- It's always April 1!
  let context : TraverseContext := {config := cfg}
  let mut iterations := 0
  repeat
    IO.println s!"Iteration {iterations} of the traversal pass"
    if iterations > 10 then
      throw <| IO.userError s!"Failed to traverse the document after {iterations} iterations. The genre is likely buggy."
    let (doc', state') ← Page.traverse doc |>.run context |>.run state
    if state == state' then break
    state := state'
    doc := doc'
    iterations := iterations + 1
  IO.println s!"Traversal completed after {iterations} iterations"

  -- Render the resulting document to HTML. This requires a way to log errors.
  let hadError ← IO.mkRef false
  let logError str := do
    hadError.set true
    IO.eprintln str

  IO.println "Rendering HTML"
  -- toHtml returns both deduplicated hover contents and the actual content.
  -- Since we're not rendering Lean code, we can ignore the hover contents.
  let (content, st) ← Page.toHtml {logError} context state {} {} {} doc .empty

  ensureDir (cfg.destination.join "flean")

  IO.FS.writeFile (cfg.destination.join "flean/verso-docs.json") (toString st.dedup.docJson)
  for (name, content) in state.jsFiles do
    ensureDir (cfg.destination.join "flean/verso-js")
    IO.FS.writeFile (cfg.destination.join "flean/verso-js" |>.join name) content
  for (name, content) in state.cssFiles do
    ensureDir (cfg.destination.join "flean/verso-css")
    IO.FS.writeFile (cfg.destination.join "flean/verso-css" |>.join name) content

  let html := {{
    <html>
      <head>
      <meta name="date" content="2025-02-27 08:32" /> -- for pelican's parsing
      <meta name="status" content="hidden" /> -- for pelican's parsing
      <meta name="tags" content="math, lean" /> -- for pelican's parsing
      <meta name="slug" content="flean2" /> -- for pelican's parsing
      <meta name="authors" content="Joseph McKinsey" /> -- for pelican's parsing
      <meta name="category" content="article" /> -- for pelican's parsing
      <meta name="summary" content="I am mostly done with flean" /> -- for pelican's parsing
      <title>{{doc.titleString}}</title>
      <meta charset="utf-8"/>
      </head>
      <body>
      {{getHeader <| getHeaderInfo state}} -- to escape pelican's parsing
      {{ content }}
      </body>
    </html>
  }}

  IO.println "Writing to index.html"
  IO.FS.withFile (cfg.destination.join "index.html") .write fun h => do
    h.putStrLn "<!DOCTYPE html>"
    h.putStrLn html.asString

  if (← hadError.get) then
    IO.eprintln "Errors occurred while rendering"
    pure 1
  else
    pure 0
