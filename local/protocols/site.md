# Site protocol — component store and local deployment

Governs `local/bin/site.sh` and `local/bin/fetch-latest-component.sh`: how the
blueprint, documentation and badge components are built, versioned, and
assembled into the served site. Read `local/protocols/meta.md` first; this
document is normative until amended through the procedure there.

Replaces, in the frozen `.github/` reference tree:

| Parent mechanism | Local replacement |
|---|---|
| `.github/workflows/blueprint.yml` | `site.sh blueprint` |
| `.github/actions/package-blueprint-component/action.yml` | packaging step inside `site.sh blueprint` |
| `.github/workflows/badges.yml` | `site.sh badges` |
| `.github/workflows/docgen.yml` (site half) | `site.sh docs` (stub; see §6) |
| `.github/workflows/deploy-pages.yml` | `site.sh assemble` |
| `scripts/fetch-latest-artifact.sh` | `local/bin/fetch-latest-component.sh` |
| `scripts/assemble-pages-site.sh` | unchanged — ported as-is and invoked by `site.sh assemble` |

Nothing here calls `gh`, needs `GH_TOKEN`/`GITHUB_REPOSITORY`, or produces
GitHub annotations. All runtime state lives under `~/.cache/mipstarre-dev/`
(`local/DESIGN.md:37-38`); generated output never enters git history, exactly as
`deploy-pages.yml:3-5` states for the parent.

## 1. The component store

The parent workflow uses the Actions artifact API as a content store keyed by
*name*: `deploy-pages.yml:26-32` fetches the newest non-expired artifact called
`site-blueprint`, `site-docs`, `site-badges`, **whichever workflow produced
it** — `site-blueprint` is uploaded by both `blueprint.yml:85-90` and
`docgen.yml:155-160`. The site is therefore not one build; it is the fibre
product of three independently refreshed components.

The local store is the same object with the API removed:

```
~/.cache/mipstarre-dev/site-components/
  site-blueprint/
    20260830T012532Z/          payload: homepage/ blueprint/ blueprint.pdf
    20260830T012532Z.stamp     provenance (key=value; never inside the payload)
    latest -> 20260830T012532Z
  site-docs/    …              payload: docs/ [paper-gaps/]
  site-badges/  …              payload: *.json
```

Definitions and their parent counterparts:

- **Version** — an immutable directory named `<UTC timestamp>` in
  `%Y%m%dT%H%M%SZ` form (with a `-1`, `-2`, … suffix on same-second
  collisions). Lexicographic order is chronological order.
- **`latest`** — the symlink that replaces "newest non-expired artifact by
  name". Publishing swaps it by `rename(2)` over a temporary symlink in the
  same directory, so a concurrent reader observes either the old target or the
  new one, never an absent pointer. (`ln -sfn` unlinks first and leaves a
  window in which a fetch would report the component as unpublished — which the
  assembler turns into a refusal, §3.)
- **Publication** — the build stages into
  `site-components/<name>/.staging.<pid>` and `mv`s it to `<timestamp>` inside
  the same directory. A same-filesystem rename is atomic, so a version
  directory is complete the instant it becomes visible.
- **Stamp** — provenance for a version: component, version, source root, source
  SHA, host, and stage-specific fields (`homepage=jekyll|raw`,
  `texra_blueprint_pin=…`, `badge_count=…`, `log=…`). It is stored *beside* the
  payload, never inside it: `assemble-pages-site.sh:67-68` copies
  `site-badges/*.json` wholesale and the non-empty guard counts `*.json`, so a
  stamp shipped in the badge payload would both serve as a fake badge endpoint
  and satisfy the guard by itself.
- **Retention** — artifact expiry (30 days for `site-blueprint`/`site-badges`,
  90 for `site-docs`) becomes a version budget: `MIPSTARRE_SITE_KEEP` (default
  3) newest versions per component, **plus** the version `latest` points at,
  which is never collected. GC runs at publication time, before the pointer
  swap, so an operator's rollback pin (§4) survives the next publish.

## 2. Producers

Each subcommand builds one component and publishes it; none of them touches the
served site.

**`site.sh blueprint`** (`blueprint.yml:31-90`)

1. `texra-blueprint bbl` at the source root — `web.bbl` is not committed and is
   regenerated from the `\cite` keys in the blueprint sources
   (`blueprint.yml:46-49`). Its log is kept separate from the render log so
   that the gates below apply to exactly the text the parent gates on.
2. `leanblueprint pdf`, then a non-empty check on `print/print.pdf`
   (`blueprint.yml:63-66`), then `texra-blueprint web`, all teed to
   `~/.cache/mipstarre-dev/site/logs/blueprint-<timestamp>.log`.
3. Two gates on that log, both fatal (`blueprint.yml:73-80`): a line matching
   `^ERROR:` means unresolved labels; `WARNING: File not found:` means missing
   files. These are *exit-code* gates. GitHub's `::error::`/`::warning::`
   annotations are inert locally, and their severity ordering is misleading:
   the second gate fails the build on a line that begins with `WARNING`.
4. Packaging (`package-blueprint-component/action.yml:13-26`):
   `blueprint/web → blueprint/`, `blueprint/print/print.pdf → blueprint.pdf`,
   and the Jekyll build of `home_page/ → homepage/`.
5. A self-check that the packaged tree satisfies every precondition
   `assemble-pages-site.sh:19-33` tests, before publishing. A published but
   unusable `latest` would block every deploy until the next successful build.

Missing `leanblueprint`/`texra-blueprint` is a hard error carrying the install
recipe (`docs/ci-automation.md:515-516` plus the `texra-blueprint` pin). Missing
Jekyll is a hard error too, with an explicit escape hatch:
`MIPSTARRE_SITE_HOMEPAGE_RAW=1` publishes `home_page/` unrendered and records
`homepage=raw` in the stamp. There is no silent fallback: a homepage of raw
Markdown must be a decision, not an accident.

**`site.sh badges`** (`badges.yml:17-45`)

Runs `scripts/generate_badges.py --output-dir <staging> --blueprint-src
blueprint/src` and refuses to publish when zero JSON files were produced —
`badges.yml:34-38` verbatim, and the reason is §3: an empty generation must
never become the newest version and blank the live badge endpoints. The
generator resolves the repository from its own path and shells out to
`git ls-files`, so it needs committed sources; CI compensates with
`fetch-depth: 0` (`badges.yml:23-24`) and a local clone already has full
history. Upstream this ran weekly (`cron '30 5 * * 0'`); locally it is on
demand or driven by whatever scheduler the operator installs.

**`site.sh docs`** — stub; see §6.

## 3. Last-known-good semantics

This is the invariant the parent workflow grew defensively
(`assemble-pages-site.sh:36,41`) and the reason the fetch shim has an unusual
contract. Three statements, in the order they are relied upon:

1. `fetch-latest-component.sh NAME DEST` exits **0 without creating `DEST`**
   when the component has never been published or `latest` dangles — the same
   contract as `fetch-latest-artifact.sh:5-6,19-20` ("callers decide whether a
   missing component is fatal").
2. `assemble-pages-site.sh` decides: it tests for the directories and hard-fails
   with *refusing to remove deployed API docs* (line 36) and *refusing to
   remove deployed badge endpoints* (line 41). The refusal is expressed by
   `DEST` not existing, so a fetch that helpfully created an empty `DEST` would
   silently disable it — the site would deploy with its API docs deleted.
3. `site.sh assemble` therefore assembles into a staging tree and swaps only on
   success. A refusal leaves the served site exactly as it was.

Consequences that must hold together:

- GC never deletes the target of `latest` (§1), because a deploy racing a GC
  pass would otherwise turn a stale component into a missing one.
- A failed producer is *not* an error for the site: `site.sh all` runs every
  producer, then assembles once, and reports the failures at the end. The
  deploy simply keeps that component's last known good version — the parent
  gets this for free by having each producer call the deployer separately.
- The corrupt-store case is distinguished from the miss case:
  `fetch-latest-component.sh` exits 1 when `latest` exists but is not a
  symlink. Deploying an unknown version is worse than not deploying.

## 4. Deployment

`site.sh assemble` fetches the three components into a private
`components/` directory, runs the unmodified
`scripts/assemble-pages-site.sh components <staging>`, and installs the result:

```
~/.cache/mipstarre-dev/site/_site           served tree
~/.cache/mipstarre-dev/site/_site.prev      previous tree (rollback)
~/.cache/mipstarre-dev/site/deployed.stamp  component version per name
```

The assembler begins with `rm -rf "$OUT"` (`assemble-pages-site.sh:45`). In CI
that is harmless because `_site` is staged before upload; locally, pointing it
at the served root would 404 a running server for the duration of the copy.
Hence the staging tree and the swap. `rename(2)` cannot replace a non-empty
directory, so the swap is two renames — old tree aside, new tree in — with a
gap of microseconds rather than seconds; the displaced tree is kept as
`_site.prev`.

Serve it however you like; the site is static:

```bash
python3 -m http.server --directory ~/.cache/mipstarre-dev/site/_site 8000
```

**Rollback.** Repoint a component at a known-good version and redeploy:

```bash
cd ~/.cache/mipstarre-dev/site-components/site-blueprint
ln -sfn 20260830T012532Z latest      # or restore ~/.cache/mipstarre-dev/site/_site.prev
local/bin/site.sh assemble
```

GC will keep that version while it is the `latest` target. `ln -sfn` is fine by
hand — it is not atomic, so do it while no deploy is in flight; the scripts
themselves always swap the pointer by rename.

## 5. Locks and ordering

The parent's cancellation policy is asymmetric on purpose
(`blueprint.yml:17-21` vs `deploy-pages.yml:14-16`), and the asymmetry is
preserved:

- **Builds do not queue.** `blueprint-build` has `cancel-in-progress: true`
  upstream because rapid pushes only need the newest render. Locally the two
  invocations would share one working tree, so the second one refuses
  immediately (`.blueprint-lock`, zero wait) instead of cancelling the first.
  Never kill a running build to start a newer one; let it finish and rebuild.
- **Deploys queue.** `github-pages-deploy` has `cancel-in-progress: false`, so
  `site.sh assemble` waits on `~/.cache/mipstarre-dev/site/.deploy-lock`
  (`MIPSTARRE_SITE_LOCK_WAIT`, default 600 s) rather than failing fast.

Both locks are `mkdir(2)` directories holding the owner's pid; a lock whose
owner is gone is reclaimed with a warning, and a lock is only ever released by
the process named in it. Staging paths carry the pid for the same reason: no
run may delete another run's work in progress.

Git-hook hygiene: every external tool is invoked through a wrapper that unsets
the variables from `git rev-parse --local-env-vars`, exactly as
`.githooks/pre-push:19-24` does. If `site.sh` is ever driven from a hook, a
leaked `GIT_DIR` would make nested git operations inside Lake or the badge
generator resolve the wrong repository.

## 6. The documentation component

`site.sh docs` prints a SKIP and exits 0. The upstream producer
(`docgen.yml`) spends a weekly 330-minute budget on a full `lake build`, a
second Lake project (`cd docbuild && lake build MIPStarRE:docs`,
`docgen.yml:142-145`), the paper-gap site (`docgen.yml:127-133`), and packaging
(`docgen.yml:150-153`). That work belongs to the build layer
(`local/protocols/build-cache.md`), not to the site assembler; duplicating it
here would violate the no-duplicate-compilation rule.

To publish a version, build out of band and hand the tree to the same command:

```bash
cd docbuild && lake build MIPStarRE:docs        # one full-build lock holder
mkdir -p /tmp/site-docs
cp -R docbuild/.lake/build/doc /tmp/site-docs/docs
texra-blueprint --root . paper-gaps site /tmp/site-docs/paper-gaps   # optional
MIPSTARRE_SITE_DOCS_DIR=/tmp/site-docs local/bin/site.sh docs
```

The import validates that the tree contains `docs/`, carries `paper-gaps/`
along when present, and records `imported_from` in the stamp. Two upstream
details to keep when this is promoted to a real producer: `docbuild` has its
own Lake project and its own cache lifecycle (`docgen.yml:135-140`), so a
persistent `docbuild/.lake/build` is the local cache, invalidated only when
`docbuild/lean-toolchain` or `docbuild/lake-manifest.json` changes; and the
ProofWidgets prune workaround (`docgen.yml:56-64`) bites on any tree without
`.lake/packages`, which is exactly the state of a pristine worktree.

Until a `site-docs` version exists, `assemble` refuses. That is the designed
behaviour, not a bug: see §3.

## 7. Triggers

The parent fires on pushes to `main` touching `blueprint/src/**`, `home_page/**`,
the two workflow files, the packaging action, and the two site scripts
(`blueprint.yml:7-14`), plus two crons (badges Sunday 05:30 UTC, docgen 06:00).
Locally nothing fires on its own: `site.sh` is invoked by the operator or by
whatever watcher the build layer installs. When such a watcher is written, it
must gate on `git diff --name-only` against that same path list, and the list
must be kept in lockstep with the scripts it protects. The parent patched its
path filters twice after discovering checks that silently never ran
(`pr-ci.yml:22-24,102-104`); a local gate has the same failure mode, and it is
silent by construction.

## 8. Invariants

Violating any of these re-introduces a documented failure of the parent
workflow.

1. A fetch miss creates no `DEST` and exits 0 (`fetch-latest-artifact.sh:5-6`).
2. GC never removes the version `latest` points at.
3. Nothing is published that would fail `assemble-pages-site.sh:19-43`;
   in particular, no empty badge set (`badges.yml:34-38`).
4. Version directories and the `latest` pointer are installed by rename, never
   built up in place.
5. Blueprint gates are exit codes on the render log, `^ERROR:` and
   `WARNING: File not found:` (`blueprint.yml:73-80`).
6. The served tree is replaced only after a successful assembly, and the
   previous tree is retained.
7. Deploys are serialized by a lock; builds refuse rather than cancel.
8. External tools run without the git hook environment.
9. Runtime state stays under `~/.cache/mipstarre-dev/`; the repository holds
   only these scripts and this protocol.

## 9. Telemetry

Render logs live in `~/.cache/mipstarre-dev/site/logs/` and are referenced from
the component stamps. Site builds are deliberately **not** written to
`results/telemetry/builds.jsonl`: `meta.md` fixes that schema's `kind` to
`warm|rebuild|cache-get|ci-build`, and a `site` kind is a protocol amendment,
not a script decision. If site-build cost turns out to be worth measuring,
follow `meta.md`'s amendment procedure and update this section together with
the schema.

## 10. Operator reference

```bash
local/bin/site.sh blueprint     # build + publish site-blueprint
local/bin/site.sh badges        # build + publish site-badges
local/bin/site.sh docs          # SKIP unless MIPSTARRE_SITE_DOCS_DIR is set
local/bin/site.sh assemble      # fetch newest components, assemble, swap
local/bin/site.sh all           # all producers, then one assemble

local/bin/fetch-latest-component.sh site-blueprint /tmp/c/site-blueprint
```

| Variable | Default | Effect |
|---|---|---|
| `MIPSTARRE_CACHE_ROOT` | `~/.cache/mipstarre-dev` | runtime state root |
| `MIPSTARRE_SITE_SOURCE_ROOT` | this checkout | tree to build from; point it at the hot-main checkout once the warmer publishes one |
| `MIPSTARRE_SITE_KEEP` | `3` | versions kept per component (minimum 1) |
| `MIPSTARRE_SITE_LOCK_WAIT` | `600` | seconds to queue for the deploy lock |
| `MIPSTARRE_SITE_HOMEPAGE_RAW` | unset | `1` publishes `home_page/` unrendered when Jekyll is absent |
| `MIPSTARRE_SITE_DOCS_DIR` | unset | tree containing `docs/` to publish as `site-docs` |
| `TEXRA_BLUEPRINT_VERSION` | `v0.3.8` | texra-blueprint pin quoted in the install hint |

Exit codes: `0` success (a SKIP is a success), `1` a stage failed or the
assembly was refused, `2` usage error. The version pin is read from
`local/bin/env.sh` when that file exists, so that the four-way cross-reference
the parent maintained by comment (`pr-ci.yml:206-208`) becomes one definition.
