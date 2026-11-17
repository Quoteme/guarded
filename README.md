# guarded

> [!CAUTION]
> currently there are LOTS of errors in this code.
> DO NOT USE IT FOR ANYTHING SERIOUS!

A small language of guarded recursive types, interpreted in the topos of
trees, together with a language server for `.grd` files written in Lean 4
using [lapis](https://github.com/SrGaabriel/lapis).

## Build

```sh
lake build
```

This produces `.lake/build/bin/guarded`.

- `guarded` runs the language server on stdin/stdout.
- `guarded check FILE.grd` prints all diagnostics, including `#eval` output.

## The language

```
-- comments start with -- or //
Bool   := (true := 1) + (false := 1)            -- labelled coproduct
Pair   := (fst := Bool) × (snd := Bool)          -- labelled product (× or *)
Stream := (val := Bool) × (tail := later Stream) -- later (or ▷) delays by one stage

p : Pair := (fst := true, snd := false)          -- global element 1 → Pair

ts : later Stream -> Stream :=                   -- guarded fixed point
  | 1 -> (val := true, tail := *)                -- stage 0: later Stream is 1
  | y -> (val := true, tail := y)                -- stage n+1 from stage n

#eval 5 ts                                       -- shows stages 5, 4, …, 0
```

- `1` and `0` are the terminal and initial objects: `1(n) = {*}`, `0(n) = ∅`.
- `(later X)(0) = 1` and `(later X)(n+1) = X(n)`. Recursive type definitions
  must be guarded: every recursive occurrence is under `later`.
- Components of sums and products are always labelled. Labels are
  constructors (`true`, `left (…)`) and fields (`(fst := …, snd := …)`, `e.fst`).
  `'` is an ordinary identifier character, so `a'` is a valid label.
- Expressions: constructors `l` / `l e`, records, `*` (also `()`), `next e`
  (`next : X → later X`), projections `e.l` (they look through `later`), and
  `match e { l x -> … | m -> … }` on sums.
- `y : later Y -> Y := | 1 -> e₀ | y -> e` is the unique fixed point: stage 0
  is `e₀`, stage `n+1` is `e` with `y` bound to stage `n`. Without a `| 1`
  branch, stage 0 is `e` with `y := *`. `#eval` warns if the two branches do not
  fit together (the family is then not natural).

Hover shows the type of the expression under the cursor and, on definitions,
the sizes `|X(0)|, |X(1)|, …`.

## Design

| file                    | role                                                                  |
| ----------------------- | --------------------------------------------------------------------- |
| `Guarded/Lexer.lean`    | tokenization (total)                                                  |
| `Guarded/Parser.lean`   | parsing (total; errors become `missing` nodes, layout-based recovery) |
| `Guarded/Syntax.lean`   | untyped AST                                                           |
| `Guarded/Types.lean`    | types, with `Ty.error` carrying diagnostics                           |
| `Guarded/Typed.lean`    | typed AST; every node stores its type                                 |
| `Guarded/Elab.lean`     | bidirectional type checking                                           |
| `Guarded/Eval.lean`     | stagewise evaluation, restriction maps, naturality check              |
| `Guarded/Analysis.lean` | pipeline, diagnostics, hover                                          |
| `Guarded/Server.lean`   | lapis glue                                                            |

Neither parsing nor type checking can fail. Every error is a `Ty.error`
stored in the typed AST, and diagnostics are read off the tree.

## Neovim (LazyVim)

`editor-integration/neovim/` provides the `guarded` filetype for `*.grd`,
syntax highlighting, the language server, and insert-mode replacements
`\later` → `▷`, `\->` → `→`, `\times` → `×`. Requires Neovim ≥ 0.11.

```lua
-- ~/.config/nvim/lua/plugins/guarded.lua
return { "Quoteme/guarded", branch = "nvim" }
```

The `nvim` branch is built by `.github/workflows/neovim-bundle.yml`: it contains
the plugin together with xz-compressed server binaries
(`bin/guarded-Linux-x86_64.xz`, `bin/guarded-Darwin-arm64.xz`). lazy.nvim runs
the plugin's `build.lua` on install and update, which unpacks the binary for
the current platform, so nothing is downloaded at runtime. `xz` must be
installed. A `guarded` executable on `$PATH` takes precedence over the bundled one.
