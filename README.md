# Convex Subgaussian

This repository contains the Lean formalization of the sharp one-dimensional
Gaussian convex comparison theorem for mean-zero real random variables with
two-sided sub-Gaussian tails.

The repository has two reader-facing surfaces:

- the source tree on `main`
- the generated GitHub Pages site with the landing page, blueprint, and Lean docs

## Repository Layout

- `ConvexSubgaussian/`: active Lean modules
- `ConvexSubgaussian.lean`: package entrypoint
- `index.html`: landing page source for the published site
- `blueprint/src/`: blueprint source
- `blueprint/web/`: checked-in published blueprint HTML
- `docbuild/`: `doc-gen4` configuration for project docs

## Build

From the repository root:

```sh
lake update
lake build
lake env lean scripts/print_axioms_check.lean
```

The axiom audit for the key endpoint theorems should report only:

- `propext`
- `Classical.choice`
- `Quot.sound`

## Additional Audits

GitHub Actions uses `leanchecker` as its kernel-replay audit:

```sh
lake env leanchecker ConvexSubgaussian.GaussianMain
lake env leanchecker ConvexSubgaussian.GaussianAsymptotics
```

## Lean Docs

The default docs build is curated: it generates Lean docs only for the
`ConvexSubgaussian` modules that are published on the Pages site.

```sh
python3 docbuild/scripts/rebuild_docs.py
```

For the older exhaustive recursive `doc-gen4` build, use:

```sh
python3 docbuild/scripts/rebuild_docs.py --mode full
```

## Blueprint

The published blueprint is served from `blueprint/web/`. To rebuild that local
HTML surface:

```sh
python3 -m venv blueprint/.venv
blueprint/.venv/bin/pip install --upgrade pip
blueprint/.venv/bin/pip install -r blueprint/requirements.txt
python3 blueprint/scripts/build_real_blueprint.py
```

## Local Site Preview

To preview the same site layout used for GitHub Pages:

```sh
python3 docbuild/scripts/rebuild_docs.py
python3 blueprint/scripts/build_real_blueprint.py
python3 scripts/assemble_pages_site.py
cd .site
python3 -m http.server 8005
```

Then open:

- `/` for the landing page
- `/blueprint/web/` for the blueprint
- `/docs/` for the Lean docs
- `/source/` for the source snapshot

## Where To Start Reading

If you want to inspect the formalized theorem statements first, start with:

- `ConvexSubgaussian/GaussianMain.lean`
- `ConvexSubgaussian/GaussianAsymptotics.lean`
- `ConvexSubgaussian/CoreDefs.lean`

`GaussianMain.lean` is the theorem-facing endpoint file. It defines:

- `AdmissibleScale`
- `cStar`
- `sharp_convexSubgaussianComparison`

`GaussianAsymptotics.lean` contains the public comparison constants and the
two named auxiliary results:

- `gaussianDomination_c0`
- `gaussianSharpness_below_c0`

## Notes

- The paper link is a placeholder until the preprint is public.
- The landing page source link is a placeholder until the final GitHub remote is fixed.
- Repository privacy is a GitHub-side setting; this source tree is prepared for an initially private repo.
- Legacy archives, local draft workspaces, and build trees are intentionally excluded from the cleaned public repo.
