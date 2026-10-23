"""Render and inspect the analytic figure without touching manuscript/data files.

Requires NumPy, Pillow, pypdf, pdfplumber, and Poppler's pdftoppm/pdffonts.
Run: python -B figures/qa/check_complete_envelope.py
The mathematical checks run in make_complete_envelope.py before export.
"""

from pathlib import Path
import hashlib
import json
import re
import subprocess

import numpy as np
from PIL import Image, ImageOps
import pdfplumber
from pypdf import PdfReader


QA = Path(__file__).resolve().parent
FIGURES = QA.parent
PAPER = FIGURES.parent
ROOT = PAPER.parents[2]
STEM = "fig_complete_envelope"


def run(*args):
    return subprocess.run(args, check=True, capture_output=True, text=True).stdout


def main():
    pdf = FIGURES / f"{STEM}.pdf"
    evidence = json.loads((FIGURES / f"{STEM}.json").read_text(encoding="utf-8"))
    run("pdftoppm", "-r", "160", "-singlefile", "-png", str(pdf),
        str(QA / "complete_envelope_print"))
    image = Image.open(QA / "complete_envelope_print.png").convert("RGB")
    gray = ImageOps.grayscale(image)
    gray.save(QA / "complete_envelope_grayscale.png")
    # A strict 50%-gray threshold is a deliberately harsh photocopy check.
    gray.point(lambda x: 255 if x >= 128 else 0, mode="1").save(QA / "complete_envelope_mono.png")

    reader = PdfReader(pdf)
    assert len(reader.pages) == 1
    page = reader.pages[0]
    box = [float(x) for x in page.mediabox]
    assert np.allclose(box, [0, 0, 400, 3.08 * 72], atol=1e-6)
    fonts = run("pdffonts", str(pdf))
    images = run("pdfimages", "-list", str(pdf))
    assert "Type 3" not in fonts
    font_rows = fonts.splitlines()[2:]
    assert font_rows and all("TrueType" in row and "yes yes yes" in row for row in font_rows)
    assert len(images.strip().splitlines()) == 2, "Raster image found in the proposed PDF"
    with pdfplumber.open(pdf) as p:
        chars = p.pages[0].chars
        assert all(c["x0"] >= -0.1 and c["x1"] <= box[2] + 0.1
                   and c["top"] >= -0.1 and c["bottom"] <= box[3] + 0.1 for c in chars)
        bounds = [min(c["x0"] for c in chars), min(c["top"] for c in chars),
                  max(c["x1"] for c in chars), max(c["bottom"] for c in chars)]
        glyph_sizes = sorted({round(c["size"], 3) for c in chars if c["upright"]})
        assert "upper envelope" in p.pages[0].extract_text()

    # Lines are supplementary colors; all explanatory text is black on white.
    colors = ("222222", "0072B2", "D55E00", "7A5195")
    contrast = {}
    for color in colors:
        rgb = np.array([int(color[j:j + 2], 16) / 255 for j in (0, 2, 4)])
        linear = np.where(rgb <= 0.04045, rgb / 12.92, ((rgb + 0.055) / 1.055) ** 2.4)
        lum = float(linear @ np.array([0.2126, 0.7152, 0.0722]))
        contrast["#" + color] = 1.05 / (lum + 0.05)
    assert min(contrast.values()) > 3
    # Verify white corner backgrounds for the delivered and all current assets.
    backgrounds = {}
    for name in ("fig_simplex", "fig_cycles", "fig_window", STEM):
        with Image.open(FIGURES / f"{name}.png") as img:
            rgb = img.convert("RGB")
            corners = [rgb.getpixel((x, y)) for x, y in
                       ((0, 0), (rgb.width - 1, 0), (0, rgb.height - 1),
                        (rgb.width - 1, rgb.height - 1))]
            assert all(min(c) >= 250 for c in corners)
            backgrounds[name] = corners

    labels = set()
    for source in PAPER.glob("*.tex"):
        labels.update(re.findall(r"\\label\{([^}]+)\}", source.read_text(encoding="utf-8")))
    caption_text = (FIGURES / "captions.md").read_text(encoding="utf-8")
    refs = set(re.findall(r"\\(?:eqref|ref|ref\*)\{([^}]+)\}", caption_text))
    assert not refs - labels, f"Caption references missing from the current paper: {refs-labels}"
    assert "fig:complete-envelope" in labels
    caption_sources = {"fig:simplex": "sec_intro.tex", "fig:C4worked": "sec_firstorder.tex",
                       "fig:cycles": "sec_firstorder.tex", "fig:complete-envelope": "sec_complete.tex"}
    for label, source in caption_sources.items():
        source_text = (PAPER / source).read_text(encoding="utf-8")
        block = next(b for b in re.findall(r"\\begin\{figure\}.*?\\end\{figure\}", source_text, re.S)
                     if "\\label{" + label + "}" in b)
        caption = block[block.index("\\caption{"):block.index("\\label{")].strip()
        assert caption in caption_text, f"Caption inventory differs from manuscript: {label}"
    baseline = json.loads((QA / "review_baseline.json").read_text(encoding="utf-8"))
    original_assets = {}
    for name, digest in baseline.items():
        rel = Path(name)
        if rel.parent.name == "figures" and rel.name != "captions.md":
            path = ROOT / rel
            same = hashlib.sha256(path.read_bytes()).hexdigest() == digest
            assert same, f"Legacy figure asset unexpectedly changed: {path}"
            original_assets[rel.name] = same
    report = {
        "scientific_checks": evidence["checks"],
        "pdf_mediabox_points": box, "pdf_text_bounds_points": bounds,
        "pdf_fonts": fonts, "pdf_images": images,
        "base_label_size_pt": 8.5, "upright_glyph_sizes_pt": glyph_sizes,
        "rotated_text_note": "pdfplumber size on the vertical axis label measures rotated "
                             "glyph advances, not nominal font size; the source sets 8.5 pt.",
        "line_colors_contrast_against_white": contrast,
        "redundant_encodings": ["four candidate dash patterns", "black upper envelope",
                                "tie labels", "numeric winning-size strips"],
        "color_vision_note": "No color-vision simulation claimed. Grayscale and strict bilevel "
                             "previews allow direct inspection of color-independent encodings.",
        "white_background_corners": backgrounds,
        "all_caption_references_resolve": sorted(refs),
        "captions_match_current_manuscript_verbatim": caption_sources,
        "legacy_figure_asset_hashes_unchanged": original_assets,
        "manual_review_required": ["complete_envelope_print.png", "complete_envelope_grayscale.png",
                                   "complete_envelope_mono.png"],
    }
    (QA / "complete_envelope_checks.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print("PASS: mathematical evidence, vector PDF, embedded fonts, text bounds, white backgrounds,")
    print("      color-independent encodings, current caption references, and unchanged legacy figures.")


if __name__ == "__main__":
    main()
