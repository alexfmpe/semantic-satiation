Cheaper: producing a program with less developer time
========

This is a catalogue of generally applicable or low-hanging ways to shorten feedback cycles between developer and codebase. Most of this boils down to leveraging performance/features of modern tooling or structuring things so as to do expensive computations less often.

Besides the direct and very expensive loss of time, focus and engagement, any noticeable delay in feedback cycles also constitutes higher-order technical debt, since when feedback cycles are large, developers are unlikely to end up sparing effort for drive-by fixes or quick wins noticed while in the course of another task. Anything that's not explicitly requested tends to end up either discarded, delayed until a later time with context and reproducibles lost, or stuck in triage/backlog for a long time, possibly costing more in overhead than it would if fixed right away.

Consider how GHC uses a strictness analyser to figure out when doing a computation right away is cheaper than doing the bookkeeping to remember to maybe do it later. In the same vein, decreasing feedback cycles allows us to be more strict more often - as things become cheaper to fix, not fixing them right away becomes more expensive in comparison.

In addition, the larger a delay, the harder it is to spot and fix increases to it, leading to two layers of [broken windows](https://blog.codinghorror.com/the-broken-window-theory/).

## Backporting

A lot of suggestions will require recent versions of GHC/HLS/Cabal. Don't delay, upgrade today.

When stuck using an old GHC for deployment, one can still get a modern tooling experience and performance improvements for development by running a parallel setup. Keep the old setup around for fixing/running CI and production builds. Note this is essentially forward-compat work as it would be needed when upgrading anyway.

If stuck on 8.x due to GHCJS in particular, consider migrating to JS or WASM backends as of GHC 9.12+. Keep in mind [jsaddle-warp](https://hackage.haskell.org/package/jsaddle-warp) allows for a GHCi-based dev workflow that can fit the parallel sidecar setup.

See [obenstein](https://github.com/alexfmpe/obenstein/blob/main/README.md) for an example of the above points.

## Building
Not specific to Haskell yet extremely useful for type-driven development: feedback at a glance without interrupting your flow/cursor to reach for squigglies
- Neovim: https://github.com/chikko80/error-lens.nvim
- VS Code: https://github.com/usernamehw/vscode-error-lens

If you notice a delay in GHCi after modules are loaded but before evaluation starts, it might be from https://gitlab.haskell.org/ghc/ghc/-/issues/23415 which is especially painful on macOS, and can be avoided by updating to one of
- 9.12.1
- 9.10.2
- 9.8.3

There's a massive correlation between GHCi "compile" time and actual compilation time. Find out the actual cost centers so as to optimize your optimization
- https://github.com/codedownio/time-ghc-modules

Throw as much of your codebase as possible into one single GHCi/HLS session to avoid expensive re-compilation of entire packages.
- https://www.well-typed.com/blog/2024/07/hls-multi/
- https://www.well-typed.com/blog/2025/06/ghci-multiple-home-units/

For lazily loading modules into GHCi
- https://cabal.readthedocs.io/en/stable/cabal-commands.html#cmdoption-repl-no-load

For faster GHCi start times and faster Template Haskell evaluation
- https://www.well-typed.com/blog/2023/02/interface-files-with-core/

For other ways of speeding up Template Haskell
- https://www.well-typed.com/blog/2025/04/explicit-level-imports/
- https://www.parsonsmatt.org/2021/07/12/template_haskell_performance_tips.html

Consult the curiously named relevant section in the GHC manual
-  [Sooner: producing a program more quickly](https://downloads.haskell.org/ghc/latest/docs/users_guide/hints.html#sooner-producing-a-program-more-quickly)

Watch out for quadratic slowdown on big records
- `makeLenses`: https://github.com/ekmett/lens/issues/986
- `deriveGeneric`: https://well-typed.com/blog/2021/08/large-records/

As a last resort, see information on setting up your module graph, which is sadly relevant for build times
- https://www.parsonsmatt.org/2019/11/27/keeping_compilation_fast.html

Hopefully by now your reloads are basically instant or at least significantly faster.
To prevent things from getting slow and unproductive again, throw in CI some regression testing of compile times.

## Running

HLS ushered in a long-awaited proper Haskell IDE experience. Another major milestone was reached recently with the upgrade of the fairly obscure GHCi debugger into something that's compatible with editors
- https://well-typed.github.io/haskell-debugger/

You might want to look for "save on run" or "run on save" settings on your editor for sinergy with the debugger.

At least until the debugger is more feature complete and [HLS is more performant](https://mercury.com/blog/announcing-ghciwatch), there is still room for the once undisputed workhorse: a GHCi based workflow wrapped in [ghcid](https://github.com/ndmitchell/ghcid) or [ghciwatch](https://mercurytechnologies.github.io/ghciwatch). Use with `--test`/`--test-ghci` respectively to evaluate any GHCi command on every save.
By default both will auto-reload on changes to haskell files and auto-restart on changes to cabal files, but you might need to learn about the relevant flags to adjust for config/asset files, more involved setup, etc
- `ghcid`: `--reload`, `--restart`
- `ghciwatch`: `--reload-glob`, `--restart-glob`

If you spend significant amounts of time after reload getting some components back to a previous state when it was only desirable to reload modified components, see
- https://github.com/ghc-proposals/ghc-proposals/pull/720

## Testing

Interactive testing is great for adding new things, but to prevent old ones from breaking we want to be able to test as much surface area as often as possible.

This can be achieved by making test suites be runnable with several degrees of reliability, say, on
1. reload
2. commit
3. CI
4. release

We can repeatedly relax the test suite in many ways, for instance
- using interpreted instead of compiled code
- decrease number of property test rounds
- skip/relax expensive properties
- generate simpler values
- pre-generate expensive data and inline it, checking staleness in CI
- call handler bindings directly bypassing (de)serialization
- use in-memory database to avoid disk access

A version of the test suite that runs in negligeable time (<0.1s) can be comfortably added to the dev cycle, e.g.
```haskell
  module Dev where
  main = runTests Fast *> yourUsualMain
```
with `cabal test` still operating as usual
```haskell
  module Test where
  main = runTests Full
```

More generally, we're dealing with an hyperrectangle, where each possible simplification is movement alongside an axis. The ideal setup allows for staying in the fast/instant region as much as possible and granularly step towards the production-grade corner only as far and long as needed (say, to fix a bug), returning back down right after. Select points in this hyperrectangle can then be used as the desired defaults for steps of the development cycle, as in the above degress-of-reliability list.
