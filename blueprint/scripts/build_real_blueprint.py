#!/usr/bin/env python3

from __future__ import annotations

import shutil
import subprocess
import sys
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
BLUEPRINT_ROOT = ROOT / "blueprint"
SRC_DIR = BLUEPRINT_ROOT / "src"
WEB_DIR = BLUEPRINT_ROOT / "web"
WEB_STYLE_DIR = WEB_DIR / "styles"
WEB_JS_DIR = WEB_DIR / "js"
SOURCE_STYLE = SRC_DIR / "extra_styles.css"
TARGET_STYLE = WEB_STYLE_DIR / "extra_styles.css"
PLASTEX_JS = WEB_JS_DIR / "plastex.js"
MODAL_FIX = """$(document).on("click", "div.modal-container", function(e) {\n        if (e.target === this) { $(this).hide(); }\n    })"""
DECL_DOC_TARGETS = {
    "AdmissibleScale": "../../docs/ConvexSubgaussian/GaussianMain.html#ConvexSubgaussian.AdmissibleScale",
    "cStar": "../../docs/ConvexSubgaussian/GaussianMain.html#ConvexSubgaussian.cStar",
    "sharp_convexSubgaussianComparison": "../../docs/ConvexSubgaussian/GaussianMain.html#ConvexSubgaussian.sharp_convexSubgaussianComparison",
    "t0": "../../docs/ConvexSubgaussian/GaussianAsymptotics.html#ConvexSubgaussian.t0",
    "A": "../../docs/ConvexSubgaussian/GaussianAsymptotics.html#ConvexSubgaussian.A",
    "B": "../../docs/ConvexSubgaussian/GaussianAsymptotics.html#ConvexSubgaussian.B",
    "a": "../../docs/ConvexSubgaussian/GaussianAsymptotics.html#ConvexSubgaussian.a",
    "p0": "../../docs/ConvexSubgaussian/GaussianAsymptotics.html#ConvexSubgaussian.p0",
    "z": "../../docs/ConvexSubgaussian/GaussianAsymptotics.html#ConvexSubgaussian.z",
    "c0": "../../docs/ConvexSubgaussian/GaussianAsymptotics.html#ConvexSubgaussian.c0",
    "gaussianScale": "../../docs/ConvexSubgaussian/GaussianAsymptotics.html#ConvexSubgaussian.gaussianScale",
    "gaussianDomination_c0": "../../docs/ConvexSubgaussian/GaussianAsymptotics.html#ConvexSubgaussian.gaussianDomination_c0",
    "gaussianSharpness_below_c0": "../../docs/ConvexSubgaussian/GaussianAsymptotics.html#ConvexSubgaussian.gaussianSharpness_below_c0",
    "layer_cake_hinge": "../../docs/ConvexSubgaussian/Internal/GaussianProof.html#OneDimConvexDom.layer_cake_hinge",
    "stopLoss_eq_integral_tail": "../../docs/ConvexSubgaussian/Internal/GaussianProof.html#OneDimConvexDom.stopLoss_eq_integral_tail",
    "stopLoss_envelope": "../../docs/ConvexSubgaussian/Internal/GaussianProof.html#OneDimConvexDom.stopLoss_envelope",
    "stopLoss_extend_all_u": "../../docs/ConvexSubgaussian/Internal/GaussianProof.html#OneDimConvexDom.stopLoss_extend_all_u",
    "convexDomination_c0_via_reduction": "../../docs/ConvexSubgaussian/Internal/GaussianProof.html#OneDimConvexDom.convexDomination_c0_via_reduction",
    "exists_unique_a": "../../docs/ConvexSubgaussian/Internal/GaussianProof.html#OneDimConvexDom.exists_unique_a",
    "J_ge_tangent_line": "../../docs/ConvexSubgaussian/Internal/GaussianProof.html#OneDimConvexDom.J_ge_tangent_line",
    "exists_extremal_measure": "../../docs/ConvexSubgaussian/Internal/GaussianProof.html#OneDimConvexDom.exists_extremal_measure",
    "muStar_isProbability": "../../docs/ConvexSubgaussian/Internal/GaussianProof.html#OneDimConvexDom.muStar_isProbability",
    "mean_muStar": "../../docs/ConvexSubgaussian/Internal/GaussianProof.html#OneDimConvexDom.mean_muStar",
    "absTail_muStar_eq_s": "../../docs/ConvexSubgaussian/Internal/GaussianProof.html#OneDimConvexDom.absTail_muStar_eq_s",
    "stopLoss_muStar_eq_J": "../../docs/ConvexSubgaussian/Internal/GaussianProof.html#OneDimConvexDom.stopLoss_muStar_eq_J",
    "gSL_eq_gClosed": "../../docs/ConvexSubgaussian/Internal/GaussianProof.html#OneDimConvexDom.gSL_eq_gClosed",
    "gaussian_tangent": "../../docs/ConvexSubgaussian/Internal/GaussianProof.html#OneDimConvexDom.gaussian_tangent",
    "gaussian_above_tangent_line": "../../docs/ConvexSubgaussian/Internal/GaussianProof.html#OneDimConvexDom.gaussian_above_tangent_line",
    "R_strict_mono_on": "../../docs/ConvexSubgaussian/Internal/GaussianProof.html#OneDimConvexDom.R_strict_mono_on",
    "monotone_ratio_principle": "../../docs/ConvexSubgaussian/Internal/GaussianProof.html#OneDimConvexDom.monotone_ratio_principle",
    "gaussian_dominates_J": "../../docs/ConvexSubgaussian/Internal/GaussianProof.html#OneDimConvexDom.gaussian_dominates_J",
}


def run(cmd: list[str], cwd: Path) -> None:
    completed = subprocess.run(cmd, cwd=cwd)
    if completed.returncode != 0:
        raise SystemExit(completed.returncode)


def sync_extra_styles() -> None:
    WEB_STYLE_DIR.mkdir(parents=True, exist_ok=True)
    shutil.copy2(SOURCE_STYLE, TARGET_STYLE)


def ensure_modal_fix() -> None:
    if not PLASTEX_JS.exists():
        raise SystemExit(f"missing expected plasTeX output: {PLASTEX_JS}")
    text = PLASTEX_JS.read_text()
    if '$(document).on("click", "div.modal-container"' in text:
        return
    marker = """    $("button.closebtn").click(
        function() {
          $(this).parent().parent().parent().hide();
        })"""
    replacement = marker + "\n    " + MODAL_FIX
    if marker not in text:
        raise SystemExit("could not find modal close button block in plastex.js")
    PLASTEX_JS.write_text(text.replace(marker, replacement))


def rewrite_lean_doc_links() -> None:
    for html_path in WEB_DIR.glob("*.html"):
        text = html_path.read_text()
        original = text
        for short_name, target in DECL_DOC_TARGETS.items():
            text = re.sub(
                rf'href="[^"]*docs/find/#doc/{re.escape(short_name)}"',
                f'href="{target}"',
                text,
            )
        if text != original:
            html_path.write_text(text)


def main() -> int:
    shutil.rmtree(WEB_DIR, ignore_errors=True)
    run([str(BLUEPRINT_ROOT / ".venv" / "bin" / "plastex"), "-c", "plastex.cfg", "web.tex"], SRC_DIR)
    sync_extra_styles()
    ensure_modal_fix()
    rewrite_lean_doc_links()
    print(f"[build_real_blueprint] wrote {WEB_DIR}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
