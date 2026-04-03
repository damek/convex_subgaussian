# Blueprint

This directory is the canonical human-facing proof map for the Gaussian part of
the formalization.

It is intentionally separate from:

- the live Lean source in `ConvexSubgaussian/`
- the public theorem endpoint in `ConvexSubgaussian/GaussianMain.lean`
- the eventual public paper link, which is still a placeholder on the landing page

## What this blueprint answers

1. What is the sharp Gaussian theorem that is formalized?
2. Which Lean declarations carry the main public result?
3. What is the proof route from the stop-loss envelope to convex domination?
4. Where does the extremal witness enter?
5. Which file owns which part of the argument?

## Source layout

- `src/`
  Blueprint-style TeX source files.
- `src/chapters/`
  Chapter-level proof-route content.
- `web/`
  Generated HTML output from the real `leanblueprint` toolchain. This directory
  is the tracked Pages artifact.
- `scripts/`
  Local rebuild wrapper for the real blueprint HTML.

## Build The Real Blueprint HTML

Install the local blueprint toolchain in the project virtual environment:

```sh
python3 -m venv blueprint/.venv
blueprint/.venv/bin/pip install --upgrade pip
blueprint/.venv/bin/pip install -r blueprint/requirements.txt
```

Then rebuild the canonical HTML:

```sh
python3 blueprint/scripts/build_real_blueprint.py
```

This writes the published artifact to:

- `blueprint/web/`

## Local preview

```sh
python3 -m http.server 8002 -d blueprint/web
```

Then open `http://localhost:8002/`.
