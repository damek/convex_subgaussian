# Blueprint

This directory contains the proof blueprint for the Gaussian convex comparison
formalization.

It is separate from:

- the Lean source in `ConvexSubgaussian/`
- the paper (placeholder on the landing page)

## What this blueprint covers

1. The sharp Gaussian theorem being formalized
2. The proof route from the stop-loss envelope to convex domination
3. Where the extremal witness enters
4. A file-by-file guide to the Lean sources

## Source layout

- `src/`
  Blueprint-style TeX source files.
- `src/chapters/`
  Chapter-level proof content.
- `web/`
  Generated HTML output from the `leanblueprint` toolchain. This directory
  is the tracked Pages artifact.
- `scripts/`
  Local rebuild wrapper for the blueprint HTML.

## Build The Blueprint HTML

Install the local blueprint toolchain in the project virtual environment:

```sh
python3 -m venv blueprint/.venv
blueprint/.venv/bin/pip install --upgrade pip
blueprint/.venv/bin/pip install -r blueprint/requirements.txt
```

Then rebuild the HTML:

```sh
python3 blueprint/scripts/build_real_blueprint.py
```

This writes the output to:

- `blueprint/web/`

## Local preview

```sh
python3 -m http.server 8002 -d blueprint/web
```

Then open `http://localhost:8002/`.
